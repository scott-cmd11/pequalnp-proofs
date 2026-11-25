import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

-- Bound edges with a sound local rectangle using the gate-charge child.
-- The remaining child concerns edges for which every candidate rectangle has junk.
theorem PEqualNP.Outside.R_meta_1780_73
    (normalize : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit),
      (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C →
      (∀ p l, I p l → circuitFun (N+N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true) →
      (∀ x, circuitFun (N+N) C x = true → ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ D.size ≤ C.size ∧ circuitFun (N+N) D = circuitFun (N+N) C ∧
        ∀ j : Fin D.size, (D.gates.get j).op = .and → ∀ i : Fin (N+N),
          (D.wires (List.ofFn fun z => decide (z = i))).getD (N+N+j.val) false = false)
    (charge : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit),
      let v : ℕ → Fin (N+N) → Bool := fun w i =>
        (C.wires (List.ofFn (fun z => decide (z = i)))).getD w false
      let cert : Fin N × Fin N → Prop := fun e => ∃ (j : Fin C.size) (k : Fin 2),
        let g := C.gates.get j
        let a := g.inputs.getD k.val 0
        let b := g.inputs.getD (1-k.val) 0
        g.op = .and ∧ v a (Fin.castAdd N e.1) = true ∧ v b (Fin.natAdd N e.2) = true ∧
        ∀ p l, v a (Fin.castAdd N p) = true → v b (Fin.natAdd N l) = true → I p l
      (∀ p p' l l', p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → (∀ j : Fin C.size, (C.gates.get j).op = .and →
        ∀ i, v (N+N+j.val) i = false) →
      ∀ E : Finset (Fin N × Fin N), (∀ e ∈ E, cert e) → E.card ≤ 4 * C.size)
    (remaining : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      let v : ℕ → Fin (N+N) → Bool := fun w i =>
        (C.wires (List.ofFn (fun z => decide (z = i)))).getD w false
      let cert : Fin N × Fin N → Prop := fun e => ∃ (j : Fin C.size) (k : Fin 2),
        let g := C.gates.get j
        let a := g.inputs.getD k.val 0
        let b := g.inputs.getD (1-k.val) 0
        g.op = .and ∧ v a (Fin.castAdd N e.1) = true ∧ v b (Fin.natAdd N e.2) = true ∧
        ∀ p l, v a (Fin.castAdd N p) = true → v b (Fin.natAdd N l) = true → I p l
      199 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, Fintype.card {p // I p l} = q + 1) →
      (∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l) →
      Monotone2 C → (∀ j : Fin C.size, (C.gates.get j).op = .and →
        ∀ i, v (N+N+j.val) i = false) →
      (∀ p l, I p l → circuitFun (N+N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true) →
      (∀ x, circuitFun (N+N) C x = true → ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true) →
      ∀ E : Finset (Fin N × Fin N), (∀ e ∈ E, I e.1 e.2 ∧ ¬ cert e) → E.card ≤ 96 * C.size) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (199 : ℕ)
      ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) →
      (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀
      (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) =>
      Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool),
      (¬∃ (x13 : Fin x2) (x14 : Fin x2), x3 x13 x14 ∧ x12 (Fin.castAdd x2 x13) = Bool.true ∧ x12 (Fin.natAdd x2 x14) =
      Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → x2 * x1 ≤ (100 : ℕ) * x5.size := by
  classical
  intro q N I inst C hq hN degree unique mono pairPos sound
  have four (p p' l l' : Fin N) (hP : p ≠ p') (hL : l ≠ l') :
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l') := by
    rintro ⟨pL, pL', p'L, p'L'⟩
    obtain ⟨t, _, only⟩ := unique p p' hP
    exact hL ((only l ⟨pL, p'L⟩).trans (only l' ⟨pL', p'L'⟩).symm)
  have positive : ∀ p l, I p l →
      circuitFun (N+N) C (pairInput (Fin.castAdd N p) (Fin.natAdd N l)) = true := pairPos
  have correct (x : Fin (N+N) → Bool) (on : circuitFun (N+N) C x = true) :
      ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
    by_contra no
    rw [sound x no] at on
    contradiction
  obtain ⟨D, monoD, le, eq, offD⟩ := normalize N I C four mono positive correct
  let v : ℕ → Fin (N+N) → Bool := fun w i =>
    (D.wires (List.ofFn (fun z => decide (z = i)))).getD w false
  let cert : Fin N × Fin N → Prop := fun e => ∃ (j : Fin D.size) (k : Fin 2),
    let g := D.gates.get j
    let a := g.inputs.getD k.val 0
    let b := g.inputs.getD (1-k.val) 0
    g.op = .and ∧ v a (Fin.castAdd N e.1) = true ∧ v b (Fin.natAdd N e.2) = true ∧
    ∀ p l, v a (Fin.castAdd N p) = true → v b (Fin.natAdd N l) = true → I p l
  let E := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  have good := charge N I D four monoD offD (E.filter cert)
    (fun e he => (Finset.mem_filter.mp he).2)
  have bad := remaining q N I D hq hN degree unique monoD offD
    (fun p l edge => by simpa only [eq] using positive p l edge)
    (fun x on => correct x (by simpa only [eq] using on))
    (E.filter (fun e => ¬ cert e)) (fun e he =>
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).2, (Finset.mem_filter.mp he).2⟩)
  have split := Finset.card_filter_add_card_filter_not (s := E) (p := cert)
  have fiber (l : Fin N) : (E.filter (fun e => e.2 = l)).card = q + 1 := by
    rw [← degree l, Fintype.card_subtype]
    apply Finset.card_bij (fun e _ => e.1)
    · intro e he
      have both := Finset.mem_filter.mp he
      have inc := (Finset.mem_filter.mp both.1).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, both.2 ▸ inc⟩
    · intro e he e' he' same
      exact Prod.ext same ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm)
    · intro p hp
      exact ⟨(p,l), by simpa [E] using (Finset.mem_filter.mp hp).2, rfl⟩
  have count : E.card = N * (q + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    simp [fiber]
  rw [count, Nat.mul_succ] at split
  omega
