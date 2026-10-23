-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_completeOND_containsCountableCompleteOND
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.completeOND_containsCountableCompleteOND
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-22T06:09:10.37768+00:00
-- url     : https://prove2.me/theorems/a7fe0031-97bf-4474-b8c7-e489d60fa461
-- title:
--   Lemma 7: countable complete OND subfamily
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. Every complete OND pure-state family $S$ in a separable space contains a countable subfamily $T$ with
--
--   $$T\subseteq S,\qquad\overline{\operatorname{span}}\{\operatorname{supp}\rho:\rho\in T\}=H,\qquad T\text{ is OND}.$$
--
--   The original family need not be countable.
--
--   This result reduces a complete OND family to a countable family with the same closed span.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 25, Lemma 7: countable complete OND subfamily

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

/-- Lemma 7, PDF p.25: a countable complete OND subfamily; no countability
hypothesis on the original family and no algebraic-span substitution. -/
theorem completeOND_containsCountableCompleteOND
    {I : Type} [Countable I] [Nonempty I]
    (S : Set (State I)) (hPure : S ⊆ pureStates I)
    (hComplete : CompleteFamily S) (hOND : OrthogonallyNondecomposable S) :
    ∃ T ⊆ S, T.Countable ∧ CompleteFamily T ∧ OrthogonallyNondecomposable T := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
