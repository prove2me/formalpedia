-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P35_oneModeZeroRegion
-- name    : QAlgorithms.Papers.Independent.Claimed50.P35.oneModeZeroRegion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:42:15.612257+00:00
-- url     : https://prove2.me/theorems/6cbb4b2f-5e8a-46c8-8489-fbd9906aa229
-- title:
--   V.B: zero-capacity noise region
-- statement:
--   For $k,N_c\ge0$, let $T$ be the actual one-mode noisy channel. If
--
--   $$N_c\ge\frac{k^2+1-|k^2-1|}{2}=\min\{1,k^2\},$$
--
--   then $Q_\Theta(T)=Q(T)=Q_\epsilon(T)=0$ for every $0\le\epsilon<1$. These are unconstrained capacities in qubits per use. The printed “max” is corrected to “min,” as required by the preceding exact threshold. This includes the vacuum replacer at $k=N_c=0$.
-- source:
--   Evaluating Capacities of Bosonic Gaussian Channels, arXiv:quant-ph/9912067v1, PDF p. 11, V.B: zero-capacity noise region

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

/-- V.B, p.11. SOURCE CORRECTION: printed max{1,k^2} becomes min{1,k^2},
equal to the preceding exact threshold (k^2+1-|k^2-1|)/2. Independent
moderation of this correction is pending. -/
theorem oneModeZeroRegion (k Nc : ℝ) (hk : 0 ≤ k) (hNc : 0 ≤ Nc)
    (hnoise : min 1 (k ^ 2) ≤ Nc) :
    transposeBound (noisyChannel k Nc) = 0 ∧ traceClassQuantumCapacity (noisyChannel k Nc) = 0 ∧
    ∀ eps : ℝ, 0 ≤ eps → eps < 1 → epsilonCapacity (noisyChannel k Nc) eps = 0 := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P35

end
