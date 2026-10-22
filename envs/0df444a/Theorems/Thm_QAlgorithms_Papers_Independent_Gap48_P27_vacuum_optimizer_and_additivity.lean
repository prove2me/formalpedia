-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_vacuum_optimizer_and_additivity
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.vacuum_optimizer_and_additivity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:15:26.844981+00:00
-- url     : https://prove2.me/theorems/ec7da5a0-0152-41a1-9f7a-608d711c8f1e
-- title:
--   Main result: vacuum optimizer and unconditional Gaussian minimum-output additivity
-- statement:
--   Let $\Phi$ be any finite-mode bosonic Gaussian gauge-covariant or gauge-contravariant channel on completed Fock spaces. Let $\mathcal S_2$ consist of all normalized positive trace-class input states with finite occupation in each mode, and let $\rho_{\rm vac}$ be the input vacuum. Write $S$ for von Neumann entropy in nats. The vacuum attains the minimum, and for every positive integer $n$,
--
--   $$
--   \min_{\rho\in\mathcal S_2}S(\Phi[\rho])=S(\Phi[\rho_{\rm vac}]),\qquad
--   \min_{\rho^{(n)}\in\mathcal S_2}S(\Phi^{\otimes n}[\rho^{(n)}])=nS(\Phi[\rho_{\rm vac}]).
--   $$
--
--   The block minimum is attained by the product vacuum and allows arbitrary entangled block inputs. For every finite nonempty heterogeneous collection $\Phi_1,\ldots,\Phi_N$ of channels of either kind, the joint minimum is attained by their product vacuum and equals both the sum of the individual minima and $\sum_jS(\Phi_j[\rho_{j,\rm vac}])$. This is unconditional: the one-mode amplifier premise is proved in §6, rather than assumed here.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 1, Main result: vacuum optimizer and unconditional Gaussian minimum-output additivity

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P27

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal BigOperators Topology ComplexOrder Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P27

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State PureState IsDensity IsTraceClass IsTraceClassChannel rankOne
   productCoeff tensorApply traceSize BreaksTraceClassEntanglement)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (extendedEntropyNats extendedRelativeEntropyNats GeneralizedEnsemble HasAverage
   finiteEnsembleCapacity ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff)

open QAlgorithms.Papers.Independent.Next46.P32
  (NumberString FockKernel vacuum productCoherentKernel modeEnergy husimi FockPOVM
   realFockTracePair)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

open QAlgorithms.Papers.Independent.Claimed50.P35
  (traceClassTensorMap traceClassChannelPower)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation partialRight partialLeft isometryCoeff conjugateKernel)

/-- Abstract, PDF pp.1,3; unconditional (26)-(27), pp.11-12, completed by §6,
p.19. Vacuum attains the minimum over all S2 inputs, including correlated
blocks and arbitrary finite nonempty heterogeneous collections. -/
theorem vacuum_optimizer_and_additivity : vacuumOptimizerAndAdditivity := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
