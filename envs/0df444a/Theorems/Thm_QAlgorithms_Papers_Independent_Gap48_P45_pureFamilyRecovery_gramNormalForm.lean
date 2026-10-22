-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pureFamilyRecovery_gramNormalForm
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.pureFamilyRecovery_gramNormalForm
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:57:49.75399+00:00
-- url     : https://prove2.me/theorems/92fd3d0e-4edc-45ef-aa51-d6c056e6b6c6
-- title:
--   Corollary 3: simplified Gram-multiplier normal form
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. For unit vectors $\eta_k$, write $G_{P,\eta}(X)=\sum_{k,l}\langle\eta_l|\eta_k\rangle P_kXP_l$. Assume either $\ker\Phi^*=\{0\}$ or $\dim H_A=\dim H_B<\infty$, and let $S$ be a complete pure family with its computed component projections. Then
--
--   $$\Phi\text{ reversible on }S\iff\Phi\text{ is unitarily equivalent to }G_{P,\eta}.$$
--
--   The vectors $\eta_k$ have norm one. In the dual-injective case every coefficient $\langle\eta_l|\eta_k\rangle$ is nonzero.
--
--   This result reduces the tensor normal form to a scalar Gram multiplier in the two stated regimes.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 17, Corollary 3: simplified Gram-multiplier normal form

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

/-- Corollary 3, PDF pp.17–18: dual injectivity OR equal finite dimensions.
Gram order is <psi_l|psi_k>; no-zero entries only when the dual is injective.
Proof typo: printed m(Phi)=1; p.7 gives m(Phi)=0 and effective multiplicity one. -/
theorem pureFamilyRecovery_gramNormalForm
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (hRegime : SimplifiedRegime Phi.val)
    (S : Set (State I)) (hPure : S ⊆ pureStates I) (hComplete : CompleteFamily S) :
    ReversibleOn Phi.val S ↔
      HasGramNormalForm Phi.val (componentProjection S) (DualInjective Phi.val) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
