-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_finiteConditionalEntropy_concavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.finiteConditionalEntropy_concavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:07:45.198978+00:00
-- url     : https://prove2.me/theorems/00ec1ff6-e5cc-4747-bcb4-74d1132ce18b
-- title:
--   Unnumbered result: concavity of finite quantum conditional entropy
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $e=\{\pi_i,\rho_i\}$ be a finite or countable ensemble on $H_A\otimes H_B$, with average $\bar\rho$ such that $H(\bar\rho)$ and $H(\operatorname{Tr}_{H_A}\bar\rho)$ are finite. Put $H_{A|B}(\tau)=H(\tau)-H(\operatorname{Tr}_{H_A}\tau)$ on this finite-entropy domain. Then the weighted series is absolutely convergent and
--
--   $$\sum_i\pi_iH_{A|B}(\rho_i)\le H_{A|B}(\bar\rho).$$
--
--   No faithful-average or rank restriction is needed.
--
--   This result expresses partial-trace information monotonicity as conditional-entropy concavity.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 22, Unnumbered result: concavity of finite quantum conditional entropy

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

/-- PDF p.22 after (21): concavity on the finite joint/marginal entropy domain.
No faithful-average assumption; absolute summability is a conclusion. -/
theorem finiteConditionalEntropy_concavity
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (e : DiscreteEnsemble (I × J))
    (hJoint : extendedEntropyNats (discreteAverageCoefficients e) < ⊤)
    (hMarginal : extendedEntropyNats (traceFirst (discreteAverageCoefficients e)) < ⊤) :
    Summable (fun i => e.weight i * separableConditionalEntropyNats (e.state i).coefficients) ∧
    (∑' i, e.weight i * separableConditionalEntropyNats (e.state i).coefficients) ≤
      separableConditionalEntropyNats (discreteAverageCoefficients e) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
