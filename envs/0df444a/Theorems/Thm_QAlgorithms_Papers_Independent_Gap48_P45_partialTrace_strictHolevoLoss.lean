-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_partialTrace_strictHolevoLoss
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.partialTrace_strictHolevoLoss
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:07:01.808613+00:00
-- url     : https://prove2.me/theorems/f175bfd9-6cd1-4bc4-911a-e2f247d7855b
-- title:
--   Proposition 4: strict Holevo loss under partial trace, discrete and continuous cases
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $H_A=H_B\otimes H_E$ and $\Phi=\operatorname{Tr}_{H_E}$. For a discrete ensemble $e=\{\pi_i,\rho_i\}$ with faithful average and finite $\chi(e)$, assume a single finite integer $r<\dim H_E$ bounds every constituent rank. For a generalized Borel ensemble $\mu$ with faithful average and finite $\chi(\mu)$, assume a single such finite $r$ bounds ranks on the entire topological support. Respectively,
--
--   $$\chi(\Phi(e))<\chi(e),\qquad\chi(\Phi(\mu))<\chi(\mu).$$
--
--   These are two separate cases. The dimension is that of the discarded factor; when it is one, the rank hypotheses are impossible for normalized states.
--
--   This result gives strict information loss under a partial trace at a faithful ensemble average.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 22, Proposition 4: strict Holevo loss under partial trace, discrete and continuous cases

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

/-- Proposition 4, PDF p.22, BOTH A and B. The bound is uniformly finite and
uses the discarded E dimension; B imposes it on topological support. -/
theorem partialTrace_strictHolevoLoss
    {B E : Type} [Countable B] [Countable E] [Nonempty B] [Nonempty E] :
    (∀ e : DiscreteEnsemble (B × E), FullRank (discreteAverageCoefficients e) →
      (∃ r : ℕ, (r : ℕ∞) < dimensionCount E ∧
        ∀ i, operatorRank (boundedOperator (e.state i).coefficients) ≤ r) →
      discreteHolevo (id : Matrix (B × E) (B × E) ℂ → Matrix (B × E) (B × E) ℂ) e < ⊤ →
      discreteHolevo (traceSecond (I := B) (J := E)) e <
        discreteHolevo (id : Matrix (B × E) (B × E) ℂ → Matrix (B × E) (B × E) ℂ) e) ∧
    (∀ mu : GeneralizedEnsemble (B × E), FullRank (averageCoefficients mu) →
      (∃ r : ℕ, (r : ℕ∞) < dimensionCount E ∧
        ∀ rho ∈ (mu : Measure (State (B × E))).support,
          operatorRank (boundedOperator rho.coefficients) ≤ r) →
      ensembleHolevo (id : Matrix (B × E) (B × E) ℂ → Matrix (B × E) (B × E) ℂ) mu < ⊤ →
      ensembleHolevo (traceSecond (I := B) (J := E)) mu <
        ensembleHolevo (id : Matrix (B × E) (B × E) ℂ → Matrix (B × E) (B × E) ℂ) mu) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
