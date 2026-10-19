-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_theorem_A_7
-- name    : QAlgorithms.Papers.Independent.Information100.P50.theorem_A_7
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:12:06.563985+00:00
-- url     : https://prove2.me/theorems/2766c884-e000-4a7f-a8b7-891b322c604d
-- title:
--   Theorem A.7: For all CP Phi,Psi, every unitarily invariant norm and p∈[1,infinity], norm_ui(J(Phi#Psi))^2≤norm_ui(J(Phi))*n
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For all CP maps $\Phi,\Psi$, every unitarily invariant matrix norm $\|\cdot\|_{ui}$, and every $p\in[1,\infty]$,
--
--   $$\|J(\Phi\#\Psi)\|_{ui}^{2}\le\|J(\Phi)\|_{ui}\|J(\Psi)\|_{ui},\qquad\|\Phi\#\Psi\|_{p\to p}^{2}\le\|\Phi\|_{p\to p}\|\Psi\|_{p\to p}.$$
--
--   The second inequality also holds for completely bounded $p\to p$ norms, defined by a supremum over every finite ancilla. In particular,
--
--   $$\|\Phi\#\Psi\|_\diamond^2\le\|\Phi\|_\diamond\|\Psi\|_\diamond.$$
--
--   Here $\#$ is the intrinsic geometric mean of CP maps. The superscript two squares the norm, and $p=\infty$ is included.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 28, Theorem A.7

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Theorem A.7, source PDF p.28, visually checked: the 2 is a square, not an index.
The norm axioms and unitary invariance of the arbitrary Choi norm are explicit. -/
theorem theorem_A_7 {dx dy : ℕ}
    (Phi Psi : Lin dx dy) (hPhi : Entanglement.IsCompletelyPositive Phi)
    (hPsi : Entanglement.IsCompletelyPositive Psi) :
    (∀ N : Matrix (Fin dy × Fin dx) (Fin dy × Fin dx) ℂ → ℝ, IsUINorm N →
      N (choiMatrix (cpGeometricMean Phi Psi)) ^ 2 ≤ N (choiMatrix Phi) * N (choiMatrix Psi)) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p →
      inducedNorm p (cpGeometricMean Phi Psi) ^ 2 ≤ inducedNorm p Phi * inducedNorm p Psi) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p →
      cbNorm p (cpGeometricMean Phi Psi) ^ 2 ≤ cbNorm p Phi * cbNorm p Psi) ∧
    cbTraceNorm (cpGeometricMean Phi Psi) ^ 2 ≤ cbTraceNorm Phi * cbTraceNorm Psi := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
