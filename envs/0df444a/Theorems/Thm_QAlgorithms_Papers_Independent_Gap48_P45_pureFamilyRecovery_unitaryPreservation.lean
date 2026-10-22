-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_pureFamilyRecovery_unitaryPreservation
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.pureFamilyRecovery_unitaryPreservation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:58:24.103365+00:00
-- url     : https://prove2.me/theorems/146f314c-877f-4ea5-ac65-4a640c12d0bc
-- title:
--   Remark 2: recovery is unitary preservation under Corollary 3 hypotheses
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Assume either $\ker\Phi^*=\{0\}$ or $\dim H_A=\dim H_B<\infty$, and let $S$ be a complete pure-state family. Then
--
--   $$\Phi\text{ reversible on }S\iff\exists\text{ unitary }U:H_A\to H_B,\quad\Phi(\rho)=U\rho U^*\quad\forall\rho\in S.$$
--
--   The printed reference to Corollary 2 is read as Corollary 3, for the reasons recorded in the moderation notes; independent moderation is pending.
--
--   This result identifies family recovery with unitary preservation in the simplified regimes.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 18, Remark 2: recovery is unitary preservation under Corollary 3 hypotheses

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

/-- Remark 2, PDF p.18. PRINTED: conditions of Corollary 2. CHANGED: conditions
of Corollary 3. WHY: the preceding proof uses those two channel conditions;
Corollary 2 permits mixed appended ancillas and cannot give unitary preservation.
This source correction requires independent moderation. -/
theorem pureFamilyRecovery_unitaryPreservation
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (hRegime : SimplifiedRegime Phi.val)
    (S : Set (State I)) (hPure : S ⊆ pureStates I) (hComplete : CompleteFamily S) :
    ReversibleOn Phi.val S ↔
      ∃ U : Hilbert I ≃ₗᵢ[ℂ] Hilbert J,
        ∀ rho ∈ S, Phi.val rho.coefficients = conjugateCoeff U.toLinearIsometry.toContinuousLinearMap rho.coefficients := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
