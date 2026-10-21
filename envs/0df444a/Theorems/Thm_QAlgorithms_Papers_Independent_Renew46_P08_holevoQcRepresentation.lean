-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P08_holevoQcRepresentation
-- name    : QAlgorithms.Papers.Independent.Renew46.P08.holevoQcRepresentation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T02:54:18.098508+00:00
-- url     : https://prove2.me/theorems/6dff3881-4bb4-4fdc-b1d3-bbca2b5253e3
-- title:
--   Unnumbered representation (51)
-- statement:
--   Let $\mu=\{p_i,\rho_i\}$ be any finite or countable ensemble of states on a nonzero separable complex Hilbert system $A$, and form $\widehat\rho_{AB}=\sum_i p_i\rho_i\otimes|i\rangle\langle i|$ with an orthonormal label basis. Then
--
--   $$\chi(\mu)=I(A:B)_{\widehat\rho}.$$
--
--   Both sides are extended nonnegative quantities defined by relative entropy. Finite average entropy and finite Shannon entropy are not needed for this representation.
-- source:
--   Tight continuity bounds for the quantum conditional mutual information, for the Holevo quantity and for capacities of quantum channels, arXiv:1512.09047v7, PDF p. 20, Unnumbered representation (51)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P08

noncomputable section

open Filter MeasureTheory

open scoped ENNReal NNReal BigOperators Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Renew46.P08

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Frontier18.P01
  (CountableStateEnsemble convexOperatorMixture)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity traceSize tensorApply productCoeff)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats
    extendedRelativeEntropyNats ensembleHolevo)

open QAlgorithms.Papers.Independent.Frontier18.P08
  (partialTraceFirst partialTraceSecond operatorTrace)

open QAlgorithms.Papers.Independent.Frontier30.P14 (conjugateKernel)

open QAlgorithms.Papers.Independent.Claimed50.P07
  (boundedCoefficients oscillatorGround oscillatorLevels oscillatorEnvelope oscillatorEntropyBounded)

open QAlgorithms.Papers.Independent.Next46.P08 (continuityRatio MajorantRegularity)

open QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- PDF p.20, (51): relative-entropy Holevo quantity equals QMI of its actual
qc representation, including infinite quantities and countably many labels. -/
theorem holevoQcRepresentation {I : Type} [Countable I] [Nonempty I] (mu : CountableStateEnsemble I) :
    countableHolevo mu = qmi (qcState mu) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P08

end
