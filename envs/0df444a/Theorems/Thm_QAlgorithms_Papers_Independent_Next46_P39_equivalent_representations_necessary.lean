-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_equivalent_representations_necessary
-- name    : QAlgorithms.Papers.Independent.Next46.P39.equivalent_representations_necessary
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:50:49.234626+00:00
-- url     : https://prove2.me/theorems/33eb2d82-f1b0-47e4-b1ca-f09a007837b6
-- title:
--   Maximal representation–multiplicity entanglement is necessary
-- statement:
--   In the compact finite-dimensional model, suppose a normalized pure input $\Psi$ and a normalized covariant seed attain the global ceiling $L=\sum_\mu d_\mu\min(d_\mu,m_\mu)$. Put $k_\mu=\min(d_\mu,m_\mu)$. Necessarily
--
--   $$c_\mu\ne0,\qquad r_\mu=k_\mu,\qquad \lambda_{\mu t}=1/k_\mu\quad(1\le t\le r_\mu)$$
--
--   for every sector $\mu$. Thus maximal entanglement across each representation–multiplicity factor is required. These are the virtual tensor factors of the group decomposition; no characterization of mixed inputs by pure Schmidt coefficients is made.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 11, §2.6 Consequence II: role of equivalent representations

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

/-- PDF p.11, Consequence II: necessity of maximal entanglement in every
representation–multiplicity block for an optimal pure input. -/
theorem equivalent_representations_necessary (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) (Xi : Matrix I I ℂ)
    (hXi : IsSeed R Xi)
    (hopt : likelihood Xi (QAlgorithms.pureDensity D.vector) = ceilingLikelihood R) :
    ∀ s, D.c s ≠ 0 ∧ D.r s = min (R.d s) (R.m s) ∧
      ∀ t, D.lam s t = (min (R.d s) (R.m s) : ℝ)⁻¹ := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
