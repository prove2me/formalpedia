-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_orbit_span_dimension
-- name    : QAlgorithms.Papers.Independent.Next46.P39.orbit_span_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:46:49.795088+00:00
-- url     : https://prove2.me/theorems/ab5bbaf3-d3cb-4a87-9586-5792b0bf1049
-- title:
--   Dimension of the cyclic orbit span
-- statement:
--   For a normalized pure input with Schmidt ranks $r_\mu$ in the complete isotypic decomposition, set $r_\mu=0$ in absent sectors. If $d_\Psi$ denotes the actual complex dimension of the span of $\{U_g\Psi:g\in G\}$, then
--
--   $$1\le d_\Psi=\sum_\mu d_\mu r_\mu.$$
--
--   The dimension is taken from the physical orbit, independently of the formula on the right. This links the accessible orbit subspace to the occupied equivalent irreducible copies.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 9, Lemma 1: dimension of the orbit span, Eq.(17)

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

/-- PDF p.9, Lemma 1, Eq.(17): dimension of the actual cyclic span;
absent sectors have r_mu=0. -/
theorem orbit_span_dimension (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) :
    0 < orbitDimension (R := R) D.vector ∧
    orbitDimension (R := R) D.vector = ∑ s, R.d s * D.r s := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
