-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_chp_loop_polytime
-- name    : QAlgorithms.DeWolf.chp_loop_polytime
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:15:26.405815+00:00
-- url     : https://prove2.me/theorems/624f7bc5-040c-4c5c-8dbf-41eba497511d
-- title:
--   The CHP simulation loop of a measurement-controlled Clifford circuit family is randomized polynomial time
-- statement:
--   Let $F$ be a family of measurement-controlled Clifford circuits with $\mathrm{rbits}(n)$ random bits, at most $\mathrm{steps}(n)$ operations and a polynomial-time controller. Let $\mathrm{simLoop}_n(s_0, \mathit{bits})$ run the controller for $\mathrm{steps}(n)$ rounds on the random bits $r = $ the first $\mathrm{rbits}(n)$ bits, applying the CHP update (as written in the statement) to the pair (stabilizer, destabilizer) tableaux and using the next unused remaining bit as the coin of each measurement. Then there is one randomized polynomial-time sampler $A$ such that for all $n$ and $x \in \{0,1\}^n$,
--
--   $$\mathrm{rbits}(n) + \mathrm{steps}(n) \le \mathrm{rbits}_A(|\mathrm{enc}(n,x)|),\qquad A.f(\mathrm{enc}(n,x)\,\|\,\mathrm{enc}(\mathit{bits})) = \mathrm{encodeTableau}\big(\mathrm{simLoop}_n((T_x, D_0), \mathit{bits}).1.1\big)$$
--
--   for every bit string of length $\mathrm{rbits}_A(|\mathrm{enc}(n,x)|)$, where $T_x$ has rows $(-1)^{x_j} Z_j$ and $D_0$ has rows $X_j$.
--
--   Role: the complexity half of the Gottesman-Knill simulation: the classical tableau simulation is computed by a polynomial-time machine.
-- source:
--   R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Section 20.3, Theorem 6 and its proof, pp. 187-188; S. Aaronson and D. Gottesman, Improved simulation of stabilizer circuits, Phys. Rev. A 70 (2004) 052328, arXiv:quant-ph/0406196, Section III (the CHP tableau algorithm)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace QAlgorithms.DeWolf

open QAlgorithms.Stabilizer QAlgorithms.Complexity

theorem chp_loop_polytime (F : MCCFamily) :
    let chpUpd : (n : ℕ) → CliffordOp n → Tableau n × Tableau n → Bool →
        (Tableau n × Tableau n) × Option Bool := fun n =>
      let px : Pauli → Bool := fun | .I => false | .X => true | .Y => true | .Z => false
      let pz : Pauli → Bool := fun | .I => false | .X => false | .Y => true | .Z => true
      let conjH : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Z) | .Y => (2, .Y) | .Z => (0, .X)
      let conjS : Pauli → ZMod 4 × Pauli := fun | .I => (0, .I) | .X => (0, .Y) | .Y => (2, .X) | .Z => (0, .Z)
      let conjP : Pauli → Pauli → ZMod 4 × Pauli := fun P Q => (if P = .I ∨ Q = .I ∨ P = Q then 0 else 2, Q)
      let conjPS : (Pauli → ZMod 4 × Pauli) → Fin n → PauliString n → PauliString n := fun f q P =>
        ⟨P.phase + (f (P.ops q)).1, Function.update P.ops q (f (P.ops q)).2⟩
      let cnotTab : Pauli → Pauli → ZMod 4 × Pauli × Pauli := fun Pc Pt =>
        (if px Pc && pz Pt && (px Pt == pz Pc) then 2 else 0,
          pauliOfBits (px Pc) (xor (pz Pc) (pz Pt)), pauliOfBits (xor (px Pt) (px Pc)) (pz Pt))
      let cnotPS : Fin n → Fin n → PauliString n → PauliString n := fun c t P =>
        ⟨P.phase + (cnotTab (P.ops c) (P.ops t)).1,
          Function.update (Function.update P.ops c (cnotTab (P.ops c) (P.ops t)).2.1) t
            (cnotTab (P.ops c) (P.ops t)).2.2⟩
      let updG : CliffordOp n → Tableau n → Tableau n := fun op T =>
        match op with
        | .pauli q P => fun j => conjPS (conjP P) q (T j)
        | .h q => fun j => conjPS conjH q (T j)
        | .s q => fun j => conjPS conjS q (T j)
        | .cnot c t _ => fun j => cnotPS c t (T j)
        | .measure _ => T
      let antiPair : Pauli → Pauli → Bool := fun a b => decide (a ≠ .I ∧ b ≠ .I ∧ a ≠ b)
      let antiB : PauliString n → PauliString n → Bool := fun P Q =>
        decide (Odd (Finset.univ.filter fun q => antiPair (P.ops q) (Q.ops q) = true).card)
      let oneP : PauliString n := ⟨0, fun _ => .I⟩
      let prodSel : (Fin n → PauliString n) → Finset (Fin n) → PauliString n := fun T s =>
        (List.ofFn fun i => if i ∈ s then T i else oneP).foldr PauliString.mul oneP
      let firstAnti : Tableau n → (Fin n → Pauli) → Option (Fin n) := fun T M =>
        (List.finRange n).reverse.find? (fun j => antiB (T j) ⟨0, M⟩)
      let detSel : Tableau n → (Fin n → Pauli) → Finset (Fin n) := fun D M =>
        Finset.univ.filter fun j => antiB (D j) ⟨0, M⟩ = true
      let updM : Tableau n → (Fin n → Pauli) → Fin n → Bool → Tableau n := fun T M p b =>
        fun j => if j = p then ⟨if b then 2 else 0, M⟩
          else if antiB (T j) ⟨0, M⟩ then (T j).mul (T p) else T j
      let updDM : Tableau n → Tableau n → (Fin n → Pauli) → Fin n → Tableau n := fun T D M p =>
        fun i => if i = p then T p else if antiB (D i) ⟨0, M⟩ then (D i).mul (T p) else D i
      fun op TD b =>
        match op with
        | .measure M =>
          match firstAnti TD.1 M with
          | some p => ((updM TD.1 M p b, updDM TD.1 TD.2 M p), some b)
          | none => (TD, some (decide ((prodSel TD.1 (detSel TD.2 M)).phase = 2)))
        | _ => ((updG op TD.1, updG op TD.2), none)
    let simLoop : (n : ℕ) → Tableau n × Tableau n → List Bool →
        (Tableau n × Tableau n) × List (Option Bool) × List Bool := fun n s0 bits =>
      (fun st : (Tableau n × Tableau n) × List (Option Bool) × List Bool =>
        match F.ctrl n (bits.take (F.rbits.eval n)) st.2.1 with
        | none => st
        | some o => ((chpUpd n o st.1 (st.2.2.headD false)).1,
            st.2.1 ++ [(chpUpd n o st.1 (st.2.2.headD false)).2],
            match o with
            | .measure _ => st.2.2.tail
            | _ => st.2.2))^[F.steps.eval n] (s0, [], bits.drop (F.rbits.eval n))
    ∃ A : RandPolyTimeSampler, ∀ (n : ℕ) (x : Qubits n),
      F.rbits.eval n + F.steps.eval n ≤ A.rbits.eval (encInput n x).length ∧
      ∀ bits : List Bool, bits.length = A.rbits.eval (encInput n x).length →
        A.f (encInput n x ++ encBits bits) =
          encodeTableau (simLoop n
            ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
              (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) bits).1.1 := by sorry

end QAlgorithms.DeWolf
