-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_finiteConditionalEntropy_strictConcavity
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.finiteConditionalEntropy_strictConcavity
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:08:31.037951+00:00
-- url     : https://prove2.me/theorems/2284d3c1-c7cc-430a-b8fe-16ad768591d9
-- title:
--   Corollary 6: strict conditional-entropy concavity at a faithful average
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $e=\{\pi_i,\rho_i\}$ be a finite or countable ensemble on $H_A\otimes H_B$. Its computed average $\bar\rho$ is faithful and satisfies $H(\bar\rho),H(\operatorname{Tr}_{H_A}\bar\rho)<\infty$. Assume the pointwise condition $\operatorname{rank}\rho_i<\dim H_A$ for every $i$. With $H_{A|B}(\tau)=H(\tau)-H(\operatorname{Tr}_{H_A}\tau)$, the weighted series is absolutely convergent and
--
--   $$\sum_i\pi_iH_{A|B}(\rho_i)<H_{A|B}(\bar\rho).$$
--
--   In infinite dimension the finite constituent ranks may be unbounded. Their entropy finiteness for positive weights follows from the average assumptions.
--
--   This result gives a rank-dependent strictness criterion for conditional-entropy concavity.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 22, Corollary 6: strict conditional-entropy concavity at a faithful average

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

/-- Corollary 6, PDF p.22: strict concavity at a faithful average. The rank
condition is POINTWISE, allowing unbounded finite ranks when H_A is infinite.
Finiteness of positive-weight component entropies is not an extra premise. -/
theorem finiteConditionalEntropy_strictConcavity
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (e : DiscreteEnsemble (I × J)) (hFullRank : FullRank (discreteAverageCoefficients e))
    (hJoint : extendedEntropyNats (discreteAverageCoefficients e) < ⊤)
    (hMarginal : extendedEntropyNats (traceFirst (discreteAverageCoefficients e)) < ⊤)
    (hRank : ∀ i, operatorRank (boundedOperator (e.state i).coefficients) < dimensionCount I) :
    Summable (fun i => e.weight i * separableConditionalEntropyNats (e.state i).coefficients) ∧
    (∑' i, e.weight i * separableConditionalEntropyNats (e.state i).coefficients) <
      separableConditionalEntropyNats (discreteAverageCoefficients e) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
