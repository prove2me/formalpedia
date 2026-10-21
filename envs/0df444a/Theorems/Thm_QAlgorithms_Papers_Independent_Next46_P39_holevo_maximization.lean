-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P39_holevo_maximization
-- name    : QAlgorithms.Papers.Independent.Next46.P39.holevo_maximization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:51:31.267703+00:00
-- url     : https://prove2.me/theorems/e6254643-a49c-4bb5-8ffc-8a91beaed4f9
-- title:
--   Pure orbit Holevo information and its maximum
-- statement:
--   Use natural logarithms and define $\chi_G(\rho)=S(\int_GU_g\rho U_g^\dagger dg)-\int_GS(U_g\rho U_g^\dagger)dg$, where $S$ is von Neumann entropy. For every normalized pure input in the compact finite-dimensional model,
--
--   $$\chi_G(|\Psi\rangle\langle\Psi|)=S(F_\Psi)\le\log d_\Psi,\qquad \chi_G(|\Psi\rangle\langle\Psi|)\le\log L.$$
--
--   Inputs of Eq.(19), with flat occupied Schmidt spectra and probabilities $d_\mu r_\mu/d_\Psi$, attain the first entropy bound. Inputs of Eq.(25) attain $\log L$, and such inputs exist, so this is the maximum over all pure inputs. No maximum over arbitrary mixed inputs is asserted. This relates the maximum-likelihood input family to orbit information.
-- source:
--   Maximum likelihood estimation for a group of physical transformations, arXiv:quant-ph/0507007v1, PDF p. 11, §2.6 Consequence III: Holevo quantity, Eqs.(26)–(28)

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

/-- PDF p.11, Eqs.(26)–(28): pure-input Holevo bound, balanced attainment,
and the maximum log L. Entropies consistently use natural logarithms. -/
theorem holevo_maximization (_finite : FiniteDimensional ℝ E) (_lie : LieGroup 𝓘(ℝ, E) ∞ G)
    (R : FiniteModel G I S) :
    (∀ D : SchmidtInput R,
      orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) = entropy (frame (R := R) D.vector) ∧
      orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) ≤
        Real.log (orbitDimension (R := R) D.vector) ∧
      (D.Balanced → orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) =
        Real.log (orbitDimension (R := R) D.vector)) ∧
      orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) ≤ Real.log (ceilingLikelihood R) ∧
      (D.OptimalShape → orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) =
        Real.log (ceilingLikelihood R))) ∧
    (∃ D : SchmidtInput R, D.OptimalShape ∧
      orbitHolevo (R := R) (QAlgorithms.pureDensity D.vector) = Real.log (ceilingLikelihood R)) := by sorry

end QAlgorithms.Papers.Independent.Next46.P39

end
