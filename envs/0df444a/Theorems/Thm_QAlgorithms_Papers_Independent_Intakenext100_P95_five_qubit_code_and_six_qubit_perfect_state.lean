-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P95_five_qubit_code_and_six_qubit_perfect_state
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P95.five_qubit_code_and_six_qubit_perfect_state
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T08:47:16.26761+00:00
-- url     : https://prove2.me/theorems/d1540300-eb99-4ab4-b1bf-e3a564d25cc8
-- title:
--   The explicit five-qubit code and six-qubit perfect state
-- statement:
--   Let $\mathcal C$ be the joint $+1$ eigenspace of $XZZXI,IXZZX,XIXZZ,ZXIXZ$, in that physical wire order. Let $P$ be the product of their four $+1$ spectral projectors, set $\lvert\widetilde0\rangle=4P\lvert00000\rangle$, and set $\lvert\widetilde1\rangle=X^{\otimes5}\lvert\widetilde0\rangle$. The encoder $M\lvert b\rangle=\lvert\widetilde b\rangle$ is isometric with range $\mathcal C$, which is an $[[5,1,3]]_2$ code of distance exactly three. Every normalized codeword has maximally mixed marginals on at most two physical qubits. Moreover,
--
--   $$\lvert\Psi\rangle=\frac{\lvert\widetilde0\rangle\lvert0\rangle+\lvert\widetilde1\rangle\lvert1\rangle}{\sqrt2}$$
--
--   is a normalized six-qubit perfect state. It is fixed with eigenvalue $+1$ by the four code checks extended by identity, by $X^{\otimes6}$, and by $Z^{\otimes6}$, and every marginal on at most three qubits is maximally mixed. This names the source’s explicit example and retains stabilizer signs.
--
--   The four generators commute and their ordered product is $ZZXIX$. The all-$X$ and all-$Z$ operators act on the displayed logical basis as Pauli $X$ and $Z$, respectively. On every vector in $\mathcal C$, the operator $-ZXZII$ and each of its five cyclic shifts have the same action as $X^{\otimes5}$. Thus the signed weight-three representatives in (A.4) are included explicitly.
-- source:
--   Holographic quantum error-correcting codes: Toy models for the bulk/boundary correspondence, arXiv:1503.06237v2, PDF p. 43, Appendix A.1: the five-qubit code and its six-qubit perfect state

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P95

namespace QAlgorithms.Papers.Independent.Intakenext100.P95

open scoped Matrix ComplexConjugate

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- PDF pp.43–45, Appendix A.1: the named five-qubit code has distance three,
its small codeword marginals are uniform, and its explicit normalized purification
is the six-qubit perfect state fixed by the six signed +1 checks in (A.5).
The logical X/Z actions and all cyclic signed weight-three X representatives from
(A.3)–(A.4) are included. Printed: |0tilde>|0> + |1tilde>|1>.
Changed: divide this tensor by sqrt(2) to obtain sixQubitState.
Why: the two codewords are orthonormal, so the printed tensor has squared norm 2;
this only chooses the unit-state representative of the source tensor up to scale. -/
theorem five_qubit_code_and_six_qubit_perfect_state :
    fiveEncoderᴴ * fiveEncoder = 1 ∧
    LinearMap.range (Matrix.toEuclideanLin fiveEncoder) = fiveCode ∧
    IsQCode 5 1 3 fiveCode ∧ HasDistance fiveCode 3 ∧
    (∀ i j : Fin 4, fiveGenerator i * fiveGenerator j = fiveGenerator j * fiveGenerator i) ∧
    fiveGenerator 0 * fiveGenerator 1 * fiveGenerator 2 * fiveGenerator 3 =
      pauliOps ![.Z, .Z, .X, .I, .X] ∧
    act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.X)) fiveLogicalZero = fiveLogicalOne ∧
    act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.X)) fiveLogicalOne = fiveLogicalZero ∧
    act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.Z)) fiveLogicalZero = fiveLogicalZero ∧
    act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.Z)) fiveLogicalOne = -fiveLogicalOne ∧
    (∀ r : Fin 5, ∀ psi ∈ fiveCode,
      act (-pauliOps (fun q : Fin 5 =>
        (![.Z, .X, .Z, .I, .I] : Fin 5 → Stabilizer.Pauli) (q + r))) psi =
      act (pauliOps (fun _ : Fin 5 => Stabilizer.Pauli.X)) psi) ∧
    (∀ psi : EuclideanSpace ℂ (Qubits 5), psi ∈ fiveCode → IsState psi →
      ∀ A : Finset (Fin 5), A.card ≤ 2 →
        subsetDensity A (pureDensity psi) = ((Fintype.card (SubsetConfig Bool A) : ℂ)⁻¹ • 1)) ∧
    IsState sixQubitState ∧ IsPerfect sixQubitState ∧
    (∀ j, act (sixGenerator j) sixQubitState = sixQubitState) ∧
    (∀ A : Finset (Fin 6), A.card ≤ 3 →
      subsetDensity A (pureDensity sixQubitState) = ((Fintype.card (SubsetConfig Bool A) : ℂ)⁻¹ • 1)) := by sorry

end

end QAlgorithms.Papers.Independent.Intakenext100.P95
