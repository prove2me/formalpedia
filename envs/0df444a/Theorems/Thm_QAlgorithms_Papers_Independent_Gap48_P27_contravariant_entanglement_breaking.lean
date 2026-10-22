-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P27_contravariant_entanglement_breaking
-- name    : QAlgorithms.Papers.Independent.Gap48.P27.contravariant_entanglement_breaking
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T23:17:08.222055+00:00
-- url     : https://prove2.me/theorems/a97b7192-b502-45e0-bfec-4b2d6dd2dc77
-- title:
--   Proposition 2: contravariant channels break entanglement
-- statement:
--   Let $\Phi$ be a Gaussian gauge-contravariant channel on completed finite-mode Fock spaces, with $\mu\ge(I+KK^*)/2$. For every separable ancillary Hilbert space $\mathcal H_R$ and every normalized positive trace-class joint state $\rho$,
--
--   $$
--   (\Phi\otimes\operatorname{Id}_R)[\rho]\text{ is separable}.
--   $$
--
--   Separability means membership in the trace-norm closed convex hull of product states, not existence of a countable product decomposition. No finite-moment restriction is imposed on this entanglement-breaking assertion. It supplies the channel property underlying the additivity arguments.
-- source:
--   A solution of the Gaussian optimizer conjecture, arXiv:1312.2251v2, PDF p. 10, Proposition 2: contravariant channels break entanglement

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

/-- Proposition 2, PDF p.10: every gauge-contravariant channel breaks
entanglement with every separable ancilla. Printed proof: mu2=I/2.
For general noise the decomposition is mu2=mu-KK*/2; the proposition's
unrestricted noise domain is unchanged. No S2 restriction is imposed here. -/
theorem contravariant_entanglement_breaking {a b : ℕ} (G : GaugeChannel a b)
    (hcontra : G.contravariant = true) :
    BreaksTraceClassEntanglement G.operation := by sorry

end QAlgorithms.Papers.Independent.Gap48.P27

end
