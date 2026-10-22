-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_entropyGain_convexity
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.entropyGain_convexity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:59:28.832449+00:00
-- url     : https://prove2.me/theorems/1bfbd52c-d47f-4266-a5fb-d5e7267037a3
-- title:
--   Remark 3: convexity of entropy gain on the finite-entropy domain
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. For a finite or countable ensemble $e=\{\pi_i,\rho_i\}$ with average $\bar\rho$, suppose both $H(\bar\rho)$ and $H(\Phi(\bar\rho))$ are finite. Define the entropy gain $g_\Phi(\tau)=H(\Phi(\tau))-H(\tau)$ on this finite-entropy domain. Its weighted series is absolutely convergent and
--
--   $$g_\Phi(\bar\rho)\le\sum_i\pi_i g_\Phi(\rho_i).$$
--
--   Only positive-weight constituents affect this identity.
--
--   This result expresses information monotonicity as convexity of finite entropy gain.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 19, Remark 3: convexity of entropy gain on the finite-entropy domain

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P45

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace QAlgorithms.Papers.Independent.Gap48.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsTraceClass IsTraceClassChannel traceSize traceClosure rankOne productCoeff tensorApply)

open QAlgorithms.Papers.Independent.Frontier18.P01 (Channel Complementary traceFirst traceSecond)

open QAlgorithms.Papers.Independent.Frontier18.P07
  (GeneralizedEnsemble averageCoefficients extendedEntropyNats extendedRelativeEntropyNats ensembleHolevo pureStates finiteEnsembleCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P18
  (operatorCoeff boundedOperator conjugateCoeff ReversibleOn IsometricallyEquivalent
   IsParsevalFrame IsKrausRepresentation)

open QAlgorithms.Papers.Independent.Claimed50.P16 (tensorRankLE)

open QAlgorithms.Papers.Independent.Next46.P31 (positiveSquareRoot)

open QAlgorithms.Papers.Independent.Next46.P42 (minimumOutputEntropy)

/-- Remark 3, PDF p.19: countable convexity of entropy gain at finite average
input/output entropy. Absolute summability is a conclusion, not a premise. -/
theorem entropyGain_convexity
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (e : DiscreteEnsemble I)
    (hInput : extendedEntropyNats (discreteAverageCoefficients e) < ⊤)
    (hOutput : extendedEntropyNats (Phi.val (discreteAverageCoefficients e)) < ⊤) :
    Summable (fun i => e.weight i * finiteEntropyGain Phi.val (e.state i).coefficients) ∧
    finiteEntropyGain Phi.val (discreteAverageCoefficients e) ≤
      ∑' i, e.weight i * finiteEntropyGain Phi.val (e.state i).coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
