-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_tensor_stable_implies_nppt_bound
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.tensor_stable_implies_nppt_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:38:19.707759+00:00
-- url     : https://prove2.me/theorems/ddfa0ba6-8680-4d1a-af3d-38cec22006cd
-- title:
--   Theorem 4: nontrivial tensor-stable positivity implies NPPT bound entanglement
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree.
--
--   If a nontrivial tensor-stable positive map $P:M_{d_1}\to M_{d_2}$ exists, then
--   $$\exists\rho_1\in M_{d_1}\otimes M_{d_1},\quad\exists\rho_2\in M_{d_2}\otimes M_{d_2}:\quad \rho_1,\rho_2\text{ are NPPT bound-entangled states}.$$
--   Each state is PSD with trace one, entangled, has a nonpositive partial transpose, and is not LOCC-distillable. These are two existence conclusions; no NPPT state is assumed beforehand. Finite-copy local filters to an entangled two-qubit state express the standard equivalent distillability criterion.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 3, Theorem 4: nontrivial tensor-stable positivity implies NPPT bound entanglement

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P37

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter MeasureTheory

-- Only the following exact definition bodies are reused from pinned accepted papers.

open QAlgorithms.Papers.Independent.Information100.P04 (gamma copies)

open QAlgorithms.Papers.Independent.Information100.P30 (MatrixMap IsPositiveMap)

open QAlgorithms.Papers.Independent.Information100.P50 (maxEigenvalue)

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond)

open QAlgorithms.Papers.Independent.Information100.P56 (normalizedChoi)

open QAlgorithms.Papers.Independent.Information100.P76 (swapMatrix)

open QAlgorithms.Papers.Independent.Next46.P39 (inverseSqrt)

namespace QAlgorithms.Papers.Independent.Bridge50.P37

attribute [local instance] Classical.propDecidable Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
  [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- Theorem 4, PDF pp.3,17--18: one NPPT bound-entangled state in EACH dimension. -/
theorem tensor_stable_implies_nppt_bound (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (h : ∃ P : MatrixMap (Fin d1) (Fin d2), TensorStable P ∧ Nontrivial P) :
    (∃ X : Mat (Fin d1 × Fin d1), NPPTBound X) ∧
    (∃ Y : Mat (Fin d2 × Fin d2), NPPTBound Y) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
