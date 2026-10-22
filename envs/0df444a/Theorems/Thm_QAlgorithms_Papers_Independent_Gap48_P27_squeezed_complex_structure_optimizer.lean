-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_squeezed_complex_structure_optimizer
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.squeezed_complex_structure_optimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:26:37.256139+00:00
-- url     : https://prove2.me/theorems/a86e18f8-3c23-409d-992d-6522f399871c
-- title:
--   §7: multimode optimizer transported to a squeezed complex structure
-- statement:
--   Let $\Phi$ be a Gaussian gauge-covariant channel in the standard compatible complex structures. Choose finite symplectic identifications $S_A,S_B$ of squeezed structures with the standard ones, with actual metaplectic implementers $U_A,U_B$. Define the transported channel and its squeezed input vacuum by
--
--   $$
--   \Phi_{\rm sq}[\rho]=U_B\Phi[U_A^*\rho U_A]U_B^*,\qquad
--   \rho_{\rm sq,vac}=U_A\rho_{\rm vac}U_A^*.
--   $$
--
--   The transported map is CPTP. The squeezed vacuum lies in $\mathcal S_2$ and attains the minimum output entropy over all normalized $\mathcal S_2$ inputs; that minimum equals $S(\Phi[\rho_{\rm vac}])$. The chosen complex structures are $S^{-1}iS$ in Weyl coordinates. This transports the optimizer for channels covariant with respect to the chosen structures; it does not assert that every Gaussian channel admits such a structure or give a capacity formula for a mismatched energy operator.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 21, §7: multimode optimizer transported to a squeezed complex structure

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

/-- §7, PDF p.21: transport the optimizer through the actual metaplectic
identifications of compatible squeezed complex structures. No claim is made
that an arbitrary Gaussian channel has such a structure, or that a mismatched
energy constraint gives the Gaussian capacity formula. The optimizing density
is constructed directly using accepted conjugateCoeff and vacuum; the frozen
Renew46.P39.squeezedVacuum is only a particular two-mode family. -/
theorem squeezed_complex_structure_optimizer {a b : ℕ} (G : GaugeChannel a b)
    (hcov : G.contravariant = false)
    (SA : SqueezedIdentification a) (SB : SqueezedIdentification b) :
    IsTraceClassChannel (squeezedChannel G SA SB) ∧
    minimizesOn (squeezedChannel G SA SB) finiteSecondMoments
      (conjugateCoeff SA.unitary.toLinearIsometry.toContinuousLinearMap (vacuum a)) ∧
    domainMinimumEntropy (squeezedChannel G SA SB) finiteSecondMoments =
      extendedEntropyNats (G.operation (vacuum a)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
