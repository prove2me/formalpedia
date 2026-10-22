-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_fixingOND_fixesGeneratedTraceClass
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.fixingOND_fixesGeneratedTraceClass
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:52:37.155419+00:00
-- url     : https://prove2.me/theorems/ce744f24-9dda-4299-a7b5-d8a946831e74
-- title:
--   Lemma 4: fixing an OND pure family fixes its entire generated trace class
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. Let $\Phi:\mathcal T(H)\to\mathcal T(H)$ fix each member of an OND pure family $S$, and let $H_0$ be its closed generated subspace. Then
--
--   $$\Phi(X)=X\qquad\text{for every }X\in\mathcal T(H_0).$$
--
--   Completeness in the original ambient space is not required; the conclusion includes nonpositive trace-class operators.
--
--   This result extends recovery from an OND family to the entire trace class of its generated support.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 14, Lemma 4: fixing an OND pure family fixes its entire generated trace class

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

/-- Lemma 4, PDF p.14: fixes ALL supported trace-class operators, not just states.
Completeness is relative to the generated subspace, not the ambient space. -/
theorem fixingOND_fixesGeneratedTraceClass
    {I : Type} [Countable I] [Nonempty I]
    (Phi : Channel I I) (S : Set (State I)) (hPure : S ⊆ pureStates I)
    (hOND : OrthogonallyNondecomposable S)
    (hFix : ∀ rho ∈ S, Phi.val rho.coefficients = rho.coefficients) :
    ∀ X, IsTraceClass X → conjugateCoeff (familyProjection S) X = X → Phi.val X = X := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
