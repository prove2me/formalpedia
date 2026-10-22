-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pureFamily_uniqueCountableONDDecomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.pureFamily_uniqueCountableONDDecomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:53:21.888509+00:00
-- url     : https://prove2.me/theorems/fb809239-be3f-4832-b6c4-38f910b5f0aa
-- title:
--   Lemma 5: unique countable orthogonal decomposition into OND components
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. Every pure-state family $S$, including the empty family, has a finite or countable collection of nonempty pairwise disjoint OND components $S_k$ such that
--
--   $$S=\bigcup_k S_k,\qquad \rho\perp\sigma\quad(\rho\in S_k,\ \sigma\in S_l,\ k\ne l).$$
--
--   This collection of subfamilies is unique, equivalently unique up to reindexing. For empty $S$ it is empty.
--
--   This result provides the unique orthogonal component decomposition used in channel classification.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 14, Lemma 5: unique countable orthogonal decomposition into OND components

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

/-- Lemma 5, PDF pp.14–15: canonical countable orthogonal OND decomposition,
unique up to permutation; the empty family has an empty collection. -/
theorem pureFamily_uniqueCountableONDDecomposition
    {I : Type} [Countable I] [Nonempty I]
    (S : Set (State I)) (hPure : S ⊆ pureStates I) :
    (componentSets S).Countable ∧ IsONDPartition S (componentSets S) ∧
      ∀ parts : Set (Set (State I)), IsONDPartition S parts → parts = componentSets S := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
