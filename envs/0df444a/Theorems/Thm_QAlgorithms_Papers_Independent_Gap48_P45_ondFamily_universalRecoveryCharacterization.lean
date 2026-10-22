-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_ondFamily_universalRecoveryCharacterization
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.ondFamily_universalRecoveryCharacterization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:51:26.187644+00:00
-- url     : https://prove2.me/theorems/1c5cf44e-87c1-4ca0-8f45-d4019cf6ab08
-- title:
--   Proposition 2: OND complete families characterize universal recovery
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. Let $S$ be a complete pure-state family in $H_A$. Quantify over every nonzero separable output space and every channel into it. Then
--
--   $$S\text{ is OND}\iff\text{every channel reversible on }S\text{ is isometrically equivalent to }X\mapsto X\otimes\sigma,$$
--
--   for some ancillary space and a fixed state $\sigma$. The ancilla and state may depend on the channel.
--
--   This result characterizes when recovering a pure family forces recovery of every input state.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 13, Proposition 2: OND complete families characterize universal recovery

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

/-- Proposition 2, PDF p.13: quantify over ALL nonzero separable output spaces;
channel (13) appends a fixed, possibly mixed ancillary state. -/
theorem ondFamily_universalRecoveryCharacterization
    {I : Type} [Countable I] [Nonempty I]
    (S : Set (State I)) (hPure : S ⊆ pureStates I) (hComplete : CompleteFamily S) :
    OrthogonallyNondecomposable S ↔
      ∀ (J : Type) [Countable J] [Nonempty J] (Phi : Channel I J), ReversibleOn Phi.val S →
        ∃ (K : Type) (_ : Countable K) (_ : Nonempty K) (sigma : State K),
          IsometricallyEquivalent Phi.val (appendingMap sigma) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
