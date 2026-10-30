-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P37_ppt_assistance_extension
-- name    : QAlgorithms.Papers.Independent.Bridge50.P37.ppt_assistance_extension
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T18:48:47.272197+00:00
-- url     : https://prove2.me/theorems/e1231ddb-bd3c-49a6-93a5-70402dc69550
-- title:
--   Unnumbered extension: the two-way bounds allow arbitrary PPT-preserving assistance
-- statement:
--   Write $M_d$ for complex $d\times d$ matrices in fixed orthonormal bases; positive means positive semidefinite. All maps are complex-linear and all dimensions are positive integers. CP means completely positive, coCP means that output transposition composed with the map is CP, and nontrivial means neither. Tensor-stable positivity means positivity at every positive tensor degree. The symbols $\|\cdot\|_\diamond$, $\|\cdot\|_1$ and $\|\cdot\|_\infty$ denote the diamond, trace and spectral norms, respectively; $*$ denotes the Hilbert--Schmidt adjoint. Choi matrices and maximally entangled projections use the normalized, reference-first convention.
--
--   For an arbitrary channel $T:M_{d_1}\to M_{d_2}$, the finite-use bound and capacity/strong-converse bounds also hold when assistance consists of arbitrary CPTP maps $L$ such that $\Gamma_{\rm out}\circ L\circ\Gamma_{\rm in}$ is CP, where $\Gamma$ transposes the whole Bob register. Thus
--   $$\epsilon\ge1-\frac{\|\vartheta_{d_2}\circ T\|_\diamond^m}{N},\qquad Q_{\rm PPT}(T)\le\log_2\|\vartheta_{d_2}\circ T\|_\diamond.$$
--   Every actual PPT-assisted scheme sequence with $m_\nu\to\infty$ and liminf rate strictly above this bound has computed errors tending exponentially to one, with a positive exponent and one eventual threshold. $Q_{\rm PPT}$ uses these actual schemes and a limsup achievable rate. LOCC and PPT assistance remain distinct classes.
-- source:
--   Positivity of linear maps under tensor powers, arXiv:1502.05630v2, PDF p. 11, Unnumbered extension: the two-way bounds allow arbitrary PPT-preserving assistance

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

/-- Explicit PPT-assistance extension, PDF p.11, applied to Lemma 4 and Theorem 7.
PPT-preserving assistance is a separate class, not a redefinition of LOCC. -/
theorem ppt_assistance_extension (d1 d2 : ℕ) [NeZero d1] [NeZero d2]
    (T : MatrixMap (Fin d1) (Fin d2)) (hT : IsChannel T) :
    (∀ K : TwoPartyCode T true,
      K.error ≥ 1 - diamond ((basisTransposeLinearMap (Fin d2)).comp T) ^ K.m / K.N) ∧
    diamondAssistedCapacity T true ≤ Real.logb 2 (diamond ((basisTransposeLinearMap (Fin d2)).comp T)) ∧
    AssistedStrongConverse T true (Real.logb 2 (diamond ((basisTransposeLinearMap (Fin d2)).comp T))) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P37

end
