-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_all_irreps_contribute
-- name    : QAlgorithms.Papers.Independent.Next46.P39.all_irreps_contribute
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:48:57.777977+00:00
-- url     : https://prove2.me/theorems/f78bd4d9-c641-4189-a042-cdb1138eade9
-- title:
--   All irreducible sectors contribute to optimal likelihood
-- statement:
--   In the compact finite-dimensional model, let $\Psi$ have the optimal form of Eq.(25), and put $k_\mu=\min(d_\mu,m_\mu)$ and $L=\sum_\mu d_\mu k_\mu$. Then every sector is occupied, its rank is $k_\mu$, and
--
--   $$|c_\mu|^2=\frac{d_\mu k_\mu}{L},\qquad d_\Psi=L.$$
--
--   There is a normalized covariant measurement attaining likelihood $\sum_\mu d_\mu k_\mu$. This is the quantitative contribution of each irrep to the optimal likelihood; mere nonzero occupancy without the prescribed weights and entanglement is not asserted to suffice.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 10, §2.6 Consequence I: all irreps contribute with their dimension

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

/-- PDF pp.10–11, Consequence I: the optimal inputs use every irrep with
its prescribed dimension-weighted contribution, and their orbit dimension is L. -/
theorem all_irreps_contribute (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) (hD : D.OptimalShape) :
    (∀ s, D.c s ≠ 0 ∧ D.r s = min (R.d s) (R.m s) ∧
      Complex.normSq (D.c s) =
        ((R.d s * min (R.d s) (R.m s) : ℕ) : ℝ) / (ceilingLikelihood R : ℝ)) ∧
    orbitDimension (R := R) D.vector = ceilingLikelihood R ∧
    (∃ Xi, IsSeed R Xi ∧ likelihood Xi (QAlgorithms.pureDensity D.vector) =
      ∑ s, (R.d s * min (R.d s) (R.m s) : ℕ)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
