-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_likelihood_dimension
-- name    : QAlgorithms.Papers.Independent.Next46.P39.likelihood_dimension
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:48:16.898994+00:00
-- url     : https://prove2.me/theorems/2e2be5a4-3785-489c-80f0-7b2af9a8ff74
-- title:
--   Likelihood versus orbit dimension, with equality characterization
-- statement:
--   Let $\Psi$ be a normalized pure input in the compact finite-dimensional model, with effective sector ranks $r_\mu$ and actual orbit dimension $d_\Psi$. Every normalized covariant seed obeys
--
--   $$p(g|g)\le d_\Psi.$$
--
--   A suitable normalized covariant measurement attains equality if and only if the sector probabilities satisfy $|c_\mu|^2=d_\mu r_\mu/d_\Psi$ and every occupied Schmidt probability equals $1/r_\mu$. Phases and Schmidt bases are arbitrary. The latter condition ranges only over actual Schmidt indices, so it has no division at an absent sector. This characterizes inputs for which orbit dimension is an attainable statistical bound, rather than asserting that all measurements attain it.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 9, Theorem 2 (relation between likelihood and dimension), Eqs.(18)–(19)

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

/-- PDF pp.9–10, Theorem 2, Eqs.(18)–(19): equality is attainable by a
suitable measurement iff the pure input has the specified balanced form. -/
theorem likelihood_dimension (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) (D : SchmidtInput R) :
    (∀ Xi, IsSeed R Xi → likelihood Xi (QAlgorithms.pureDensity D.vector) ≤
      orbitDimension (R := R) D.vector) ∧
    ((∃ Xi, IsSeed R Xi ∧ likelihood Xi (QAlgorithms.pureDensity D.vector) =
      orbitDimension (R := R) D.vector) ↔ D.Balanced) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
