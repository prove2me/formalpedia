-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P18_complemented_outputs_pairwise_separable
-- name    : QAlgorithms.Papers.Independent.Support21.P18.complemented_outputs_pairwise_separable
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T04:51:04.60303+00:00
-- url     : https://prove2.me/theorems/2c7b1b78-4623-459f-ae6f-02ed57b5a640
-- title:
--   Pairwise separability of complemented outputs
-- statement:
--   Let $N\ge1$, $M\ge2$, and let $\psi$ be a unit qubit vector. Form the explicit joint quantum output $q_{NM}(\psi)$ of Eqs. (7),(8), with the signed binomial amplitudes and the Eq. (1) complement convention. For any distinct sites $i,j$ among the $M$ complemented outputs in register $c$, their reduced state is separable:
--   $$
--   \rho_{c_i c_j}=\sum_{r=1}^{R}w_r\,A_r\otimes B_r,
--   \qquad w_r\ge0,\quad\sum_{r=1}^{R}w_r=1,
--   $$
--   for some finite $R$ and one-qubit density operators $A_r,B_r$.
--
--   The assertion describes each pair of complemented output sites after discarding all other qubits.
-- source:
--   Optimal Manipulations with Qubits: Universal NOT Gate, arXiv:quant-ph/9901053v1, PDF p. 3, Quantum scenario: pairwise separability of the complemented outputs

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P18

noncomputable section

namespace QAlgorithms.Papers.Independent.Support21.P18

open MeasureTheory Filter

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- PDF p.3, sentence crossing columns: every distinct pair of complemented
outputs c is separable. M>=2 makes the pair claim substantive. -/
theorem complemented_outputs_pairwise_separable (N M : ℕ) (hN : 1 ≤ N) (hM : 2 ≤ M)
    (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : IsState psi)
    (i j : Fin M) (hij : i ≠ j) :
    Entanglement.IsSeparableDensity (pairReduction (quantumComplements N M psi) i j) := by sorry

end QAlgorithms.Papers.Independent.Support21.P18

end
