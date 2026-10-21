-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_reference_dimension
-- name    : QAlgorithms.Papers.Independent.Next46.P39.reference_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:53:04.425994+00:00
-- url     : https://prove2.me/theorems/038807a9-9533-406d-ba5d-a07cfdeae47b
-- title:
--   The least saturating reference dimension
-- statement:
--   For positive irrep dimensions and multiplicities in the compact finite-dimensional model, define
--
--   $$\overline d_R=\max_{\mu\in S}\left\lceil\frac{d_\mu}{m_\mu}\right\rceil.$$
--
--   This is positive. For every positive integer $n$, all inequalities $m_\mu n\ge d_\mu$ hold if and only if $n\ge\overline d_R$. Equivalently, the actual assisted optimum equals $\sum_\mu d_\mu^2$, with a universal measurement bound and pure-state attainment, exactly for those dimensions. The ceiling means the least integer greater than or equal to its argument. In particular a ratio equal to one needs reference dimension one.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 12, Corollary 1 (dimension of the reference system), Eq.(29)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P39

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P39

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder Matrix.Norms.L2Operator Manifold ContDiff

open QAlgorithms.Measurements (DensityPOVM)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

attribute [local instance] Classical.propDecidable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Next46.P39.operatorMatrixBorel

variable {G I S : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype S] [DecidableEq S] [Nonempty S]

variable (R : FiniteModel G I S)

variable {R}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [ChartedSpace E G]

/-- PDF p.12, Corollary 1, Eq.(29). The mathematical ceiling is non-strict,
contrary to the prose 'greater than'. The threshold is the least positive
reference dimension reaching the operational saturation value. -/
theorem reference_dimension (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) :
    0 < referenceThreshold R ∧
    (∀ n, 0 < n →
      ((∀ s, R.d s ≤ R.m s * n) ↔ referenceThreshold R ≤ n)) ∧
    (∀ n, 0 < n →
      (AssistedMaximum R n (∑ s, ((R.d s) ^ 2 : ℕ)) ↔ referenceThreshold R ≤ n)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
