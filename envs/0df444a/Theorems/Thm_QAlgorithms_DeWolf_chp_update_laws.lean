-- Prove2me | Theorems.Thm_QAlgorithms_DeWolf_chp_update_laws
-- name    : QAlgorithms.DeWolf.chp_update_laws
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:13:26.391129+00:00
-- url     : https://prove2.me/theorems/8c4934c1-837f-495c-90f4-98b2fc633fb6
-- title:
--   Correctness of the CHP stabilizer-tableau update for Clifford gates and Pauli measurements
-- statement:
--   Let $\mathrm{chp}_n(op,(T,D),b)$ be the Aaronson-Gottesman (CHP) update of a pair (stabilizer tableau $T$, destabilizer tableau $D$) of $n$-qubit Pauli strings under a Clifford operation $op$ (a Pauli on one wire, $H$, $S$, CNOT, or the measurement of a Pauli string $M$), with coin $b$ used as the outcome of a random measurement, written out in full in the statement. Then there is an invariant $\mathrm{Inv}_n$ on pairs $(T,D)$ such that
--
--   $$\mathrm{Inv}_n(T_x, D_0),\qquad \prod_j \tfrac{I + (-1)^{x_j} Z_j}{2} = |x\rangle\langle x|,$$
--
--   the invariant is preserved by every update and implies that $T$ is a valid stabilizer tableau, a gate $U$ maps $\Pi_T$ to $U\Pi_T U^\dagger$ (no outcome), and a measurement of $M$ returns $\beta$ with either $\mathrm{tr}(P_\beta \Pi_T) = 1$ and the update independent of the coin (deterministic case), or $\mathrm{tr}(P_1\Pi_T) = 1/2$ and $\beta = b$ (random case), and the new projector is $\mathrm{tr}(P_\beta\Pi_T)^{-1} P_\beta \Pi_T P_\beta$, where $P_\beta = (I + (-1)^\beta M)/2$ and $\Pi_T = \prod_j (I + T_j)/2$.
--
--   Role: the quantum-mechanical half of the Gottesman-Knill simulation: the classical tableau update tracks the stabilizer state of the circuit exactly, including Born probabilities of measurements.
-- source:
--   R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Section 20.3, Theorem 6 and its proof, pp. 187-188; S. Aaronson and D. Gottesman, Improved simulation of stabilizer circuits, Phys. Rev. A 70 (2004) 052328, arXiv:quant-ph/0406196, Section III (the CHP tableau algorithm)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Stabilizer

namespace QAlgorithms.DeWolf

open QAlgorithms.Stabilizer QAlgorithms.Complexity

theorem chp_update_laws :
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
    ∃ Inv : (n : ℕ) → Tableau n × Tableau n → Prop, ∀ n : ℕ,
      (∀ x : Qubits n,
        Inv n ((fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n),
          (fun j => ⟨0, fun q => if q = j then .X else .I⟩ : Tableau n)) ∧
        tableauProjector (fun j => ⟨if x j then 2 else 0, fun q => if q = j then .Z else .I⟩ : Tableau n) =
          pureDensity (ket x)) ∧
      (∀ op s b, Inv n s → Inv n (chpUpd n op s b).1) ∧
      (∀ s, Inv n s → IsValidTableau s.1) ∧
      (∀ (op : CliffordOp n) s b, Inv n s → (∀ M, op ≠ .measure M) →
        (chpUpd n op s b).2 = none ∧
        tableauProjector (chpUpd n op s b).1.1 = op.mat * tableauProjector s.1 * op.mat.conjTranspose) ∧
      (∀ (M : Fin n → Pauli) s b, Inv n s →
        ∃ β, (chpUpd n (.measure M) s b).2 = some β ∧
          (((((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace = 1 ∧
              ∀ b', chpUpd n (.measure M) s b' = chpUpd n (.measure M) s b) ∨
            ((((2⁻¹ : ℂ) • (1 + (if true then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace = 2⁻¹ ∧ β = b)) ∧
          tableauProjector (chpUpd n (.measure M) s b).1.1 =
            (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1).trace⁻¹ • (((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ) * tableauProjector s.1 * ((2⁻¹ : ℂ) • (1 + (if β then -1 else 1) • PauliString.toMatrix ⟨0, M⟩) :
            Matrix (Qubits n) (Qubits n) ℂ))) := by sorry

end QAlgorithms.DeWolf
