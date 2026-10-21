-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_orbit_projector
-- name    : QAlgorithms.Papers.Independent.Next46.P39.orbit_projector
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:44:39.884294+00:00
-- url     : https://prove2.me/theorems/91ac4e83-949b-4db9-9d10-b7ea1f72f33c
-- title:
--   The orbit projector and compression of measurements
-- statement:
--   Use the same compact finite-dimensional group model, and write a normalized pure input as $\Psi=\bigoplus_\mu c_\mu\sum_{t=1}^{r_\mu}\sqrt{\lambda_{\mu t}}\,\psi_{\mu t}\otimes\phi_{\mu t}$, with orthonormal Schmidt factors, positive probabilities summing to one in occupied sectors, and $r_\mu=0$ exactly when $c_\mu=0$. Then
--
--   $$P_\Psi=\bigoplus_\mu I_{d_\mu}\otimes\sum_{t=1}^{r_\mu}|\phi_{\mu t}\rangle\langle\phi_{\mu t}|$$
--
--   is the orthogonal projector onto $\operatorname{span}\{U_g\Psi:g\in G\}$. This span is contained in every invariant complex subspace containing $\Psi$. Two normalized covariant seeds having the same compression $P_\Psi\Xi P_\Psi$ give identical outcome densities at every estimated and true group parameter. Thus only the compressed seed affects this orbit's statistics.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 7, §2.5, Eq.(13): projector onto the cyclic orbit subspace

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

/-- PDF p.7, Eq.(13) and following paragraph: explicit projector, cyclic span,
minimality, and dependence of all orbit outcome densities only on compression. -/
theorem orbit_projector (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) :
    D.projectorᴴ = D.projector ∧ D.projector * D.projector = D.projector ∧
    LinearMap.range (Matrix.toEuclideanLin D.projector) = cyclicSpan (R := R) D.vector ∧
    (∀ K : Submodule ℂ (EuclideanSpace ℂ I), D.vector ∈ K →
      (∀ g v, v ∈ K → QAlgorithms.act (R.U g : Matrix I I ℂ) v ∈ K) →
      cyclicSpan (R := R) D.vector ≤ K) ∧
    (∀ Xi Zeta, IsSeed R Xi → IsSeed R Zeta →
      D.projector * Xi * D.projector = D.projector * Zeta * D.projector →
      ∀ g h, QAlgorithms.effectProb (densityOrbit R Xi h)
          (densityOrbit R (QAlgorithms.pureDensity D.vector) g) =
        QAlgorithms.effectProb (densityOrbit R Zeta h)
          (densityOrbit R (QAlgorithms.pureDensity D.vector) g)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
