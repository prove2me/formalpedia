-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_idealNormalization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.idealNormalization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:29:51.63374+00:00
-- url     : https://prove2.me/theorems/802fc26f-d8c8-45d4-ae25-5cb0d42404ee
-- title:
--   II.B: ideal channel normalization
-- statement:
--   For every integer $n\ge1$, let $\operatorname{id}_n$ be the identity channel on the full $n$-dimensional matrix algebra. With capacities measured in qubits per use,
--
--   $$Q_\Theta(\operatorname{id}_n)=Q(\operatorname{id}_n)=\log_2 n.$$
--
--   The quantum capacity uses vanishing completely bounded trace-norm error and asymptotically diverging block lengths. In particular the one-dimensional identity has value zero. This fixes the normalization of the general capacity bound.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 4, II.B: ideal channel normalization

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P35

noncomputable section

open Filter MeasureTheory

open scoped Topology ENNReal NNReal BigOperators

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Claimed50.P35

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Dependency50.P39
  (displacementMatrix attenuatorMatrix amplifierMatrix thermalMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (Operation conjugateKernel composeKernel partialRight isometryCoeff identityCoeff)

open QAlgorithms.Papers.Independent.Frontier30.P21 (bosonicEntropy)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

/-- II.B, p.4: ideal normalization; n=1 gives zero. -/
theorem idealNormalization (n : ℕ) (hn : 0 < n) :
    transposeBound (id : Operation (Fin n) (Fin n)) = ENNReal.ofReal (Real.logb 2 n) ∧
    traceClassQuantumCapacity (id : Operation (Fin n) (Fin n)) = ENNReal.ofReal (Real.logb 2 n) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
