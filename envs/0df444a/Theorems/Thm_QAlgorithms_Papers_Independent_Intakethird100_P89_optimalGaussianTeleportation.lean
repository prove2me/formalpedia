-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_optimalGaussianTeleportation
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.optimalGaussianTeleportation
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:18:15.733726+00:00
-- url     : https://prove2.me/theorems/ffe18a23-ba90-4b3d-a3a8-0fb18bb61448
-- title:
--   Optimal Gaussian-prior teleportation at fixed logarithmic negativity
-- statement:
--   Let $\lambda>0$ and $r\ge0$ be finite real numbers. Coherent states $|\alpha\rangle$ are sampled with density $(\lambda/\pi)e^{-\lambda|\alpha|^2}$ against planar Lebesgue measure. A phase-insensitive Gaussian channel has transmissivity $\tau\ge0$, noise $y\ge|1-\tau|$, and no extra displacement. Let $A_r$ be the closed region additionally satisfying $y\ge e^{-2r}(1+\tau)$. Let $F_\lambda(\tau,y)=2\lambda/[2(1-\sqrt\tau)^2+\lambda(1+y+\tau)]$.
--
--   Put $t=\max\{\tanh r,e^{2r}/(e^r+\lambda\cosh r)^2\}$ and $z=e^{-2r}(1+t)$. Then $(t,z)\in A_r$ and
--
--   $$\max_{(\tau,y)\in A_r}F_\lambda(\tau,y)=\sup_{\mathcal P}\overline F_\lambda(\mathcal P)=\begin{cases}\dfrac{\lambda}{\lambda+(1-\sqrt{\tanh r})^2},&\tanh r\ge\dfrac{e^{2r}}{(e^r+\lambda\cosh r)^2},\\[4pt]\dfrac{e^r(1+\lambda+\tanh r)}{2e^r+\lambda\cosh r},&\text{otherwise}.\end{cases}$$
--
--   Here $\mathcal P$ ranges over deterministic BK protocols with positive gain and actual normalized centered two-mode Gaussian resources of finite mean energy and logarithmic negativity exactly $2r$, inducing phase-insensitive channels. The protocol fidelity is the actual prior integral of the squared coherent-state overlap. This set of fidelities is nonempty and bounded above. The channel $(t,z)$ attains the scalar maximum, and every physical channel in $A_r$ obeys the displayed bound for its actual average fidelity.
--
--   This identifies the operational supremum without assuming a finite-energy maximizer in the boundary branch.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 1, Main result: optimal Gaussian-prior coherent-state teleportation, Eq. (13)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.1 abstract and p.4, (13): maximum over the closed region equals
the independently defined supremum of ACTUAL finite-energy Gaussian BK
fidelities. The optimum need not be attained by a finite-energy resource. -/
theorem optimalGaussianTeleportation (lambda r : ℝ) (hlambda : 0 < lambda) (hr : 0 ≤ r) :
    (optimalTau lambda r, optimalNoise lambda r) ∈ entanglementAccessibleRegion r ∧
    phaseInsensitiveFidelityFormula lambda (optimalTau lambda r) (optimalNoise lambda r) =
      optimumClosedForm lambda r ∧
    IsGreatest (scalarValues lambda r) (optimumClosedForm lambda r) ∧
    scalarOptimum lambda r = optimumClosedForm lambda r ∧
    (finiteBKValues lambda r).Nonempty ∧ BddAbove (finiteBKValues lambda r) ∧
    IsLUB (finiteBKValues lambda r) (optimumClosedForm lambda r) ∧
    finiteBKOptimum lambda r = optimumClosedForm lambda r ∧
    (∀ (tau y : ℝ) (Phi : OscillatorChannel), (tau, y) ∈ entanglementAccessibleRegion r →
      PhaseInsensitive Phi tau y →
      Integrable (fun alpha => priorDensity lambda alpha * teleportedCoherentOverlap Phi alpha) ∧
      gaussianPriorFidelity lambda Phi ≤ optimumClosedForm lambda r) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
