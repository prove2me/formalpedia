-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_discreteHolevoEquality_recovery
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.discreteHolevoEquality_recovery
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:00:55.698453+00:00
-- url     : https://prove2.me/theorems/d399cdcc-a3e1-45b2-b82a-7121220c35b7
-- title:
--   Unnumbered result: finite-Holevo equality iff recovery of the ensemble family
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $e=\{\pi_i,\rho_i\}$ be a finite or countable ensemble, with computed average $\bar\rho$ and finite Holevo quantity $\chi(e)=\sum_i\pi_iD(\rho_i\|\bar\rho)$. Then
--
--   $$\chi(\Phi(e))=\chi(e)\iff\exists\text{ channel }\Theta,\quad\Theta(\Phi(\rho_i))=\rho_i\quad\text{whenever }\pi_i>0.$$
--
--   This result characterizes when a channel preserves the distinguishability of a discrete ensemble.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 19, Unnumbered result: finite-Holevo equality iff recovery of the ensemble family

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

/-- PDF p.19, after Remark 3: finite-Holevo equality iff one common channel
recovers every positive-weight state. Zero-weight entries are removed. -/
theorem discreteHolevoEquality_recovery
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (e : DiscreteEnsemble I)
    (hFinite : discreteHolevo (id : Matrix I I ℂ → Matrix I I ℂ) e < ⊤) :
    discreteHolevo Phi.val e = discreteHolevo (id : Matrix I I ℂ → Matrix I I ℂ) e ↔
      ReversibleOn Phi.val (activeStates e) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
