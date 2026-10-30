-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P22_characteristic_and_displacement
-- name    : QAlgorithms.Papers.Independent.Advance50.P22.characteristic_and_displacement
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T12:10:20.788831+00:00
-- url     : https://prove2.me/theorems/8642e078-583b-462e-a2bf-bbc3422ce5c0
-- title:
--   Section III B, Eq.(26) and following display: scattering and displacements
-- statement:
--   Let $n,K\ge1$, let $\Phi$ be a Gaussian linear scattering channel with real blocks $M_\alpha$, and let $\rho_\alpha$ be independent normalized full $n$-mode densities. For $q\in\mathbb R^{2n}$ and arbitrary input displacements $x_\alpha$, write $y=\sum_\alpha M_\alpha x_\alpha$. Then
--
--   $$\chi_Y(q)=\prod_\alpha\chi_\alpha(M_\alpha^Tq),\qquad \Phi\!\left(\bigotimes_\alpha D_{x_\alpha}\rho_\alpha D_{x_\alpha}^\dagger\right)=D_y\Phi\!\left(\bigotimes_\alpha\rho_\alpha\right)D_y^\dagger.$$
--
--   These are full characteristic and density identities; agreement of first moments alone is insufficient.
-- source:
--   The multi-mode quantum Entropy Power Inequality, arXiv:1408.6410v2, PDF p. 4, Section III B, Eq.(26) and following display: scattering and displacements

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P22

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

namespace QAlgorithms.Papers.Independent.Advance50.P22

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov PhysicalCovariance FiniteMeanEnergy
   productWeyl weylArgument multimodeWeylTrace)

open QAlgorithms.Papers.Independent.Frontier30.P08
  (QuadratureIndex interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Next46.P17
  (bosonicEntropyPower conjugateCoefficient firstMoments quadratureCovariance
   gaussianCoefficient gaussification)

open QAlgorithms.Papers.Independent.Information100.P49 (symplecticEntropy)

/-- PDF p.4, Section III B, (26) and following display: full product
characteristic and actual state displacement covariance with y=sum M_a*x_a. -/
theorem characteristic_and_displacement {n K : ℕ} (hn : 0 < n) (hK : 0 < K)
    (C : Scattering n K) (rho : Fin K → State (FockIndex n)) :
    (∀ q : InterleavedCoordinateVector n,
      multimodeWeylTrace (C.channel (independentInput (fun a => (rho a).coefficients))) q =
        ∏ a, multimodeWeylTrace (rho a).coefficients ((C.block a).transpose.mulVec q)) ∧
    (∀ x : Fin K → InterleavedCoordinateVector n,
      C.channel (independentInput (fun a => translateDensity (x a) (rho a).coefficients)) =
        translateDensity (∑ a, (C.block a).mulVec (x a))
          (C.channel (independentInput (fun a => (rho a).coefficients)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P22

end
