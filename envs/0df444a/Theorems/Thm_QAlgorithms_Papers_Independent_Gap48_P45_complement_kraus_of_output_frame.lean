-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complement_kraus_of_output_frame
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.complement_kraus_of_output_frame
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:04:10.631449+00:00
-- url     : https://prove2.me/theorems/e53ba65e-e852-405c-867a-104e97ea2972
-- title:
--   Complementary Kraus operators from a rank-one resolution of the output projection
-- statement:
--   Let $\Phi,\Psi$ be complementary channels and $P$ the projection onto the output space of $\Phi$. If a countable family $(\psi_k)$ satisfies $\sum_k|\langle\psi_k,x\rangle|^2=\langle x,Px\rangle$ for all $x$, then $\Psi$ has a Kraus representation $(V_k)$ with
--
--   $$\operatorname{rank}V_k\le\operatorname{rank}\Phi^*(|\psi_k\rangle\langle\psi_k|)\quad\text{for every }k .$$
--
--   Role: converts the rank-one pieces of the output resolution into Kraus operators $V_k=(\langle\psi_k|\otimes 1)V$ of the complementary channel with controlled rank.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3 (PDF pp. 8-9: Kraus operators of the complementary channel A_k = (<psi_k| x I) V built from a resolution of the output support, with rank A_k = rank Phi*(|psi_k><psi_k|))

import Mathlib
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

theorem complement_kraus_of_output_frame {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (K : Type) [Countable K] (psi : K → Hilbert J)
    (hpsi : ∀ x, HasSum (fun k => ‖inner ℂ (psi k) x‖ ^ 2)
      (inner ℂ x (outputProjection Phi.val x)).re) :
    ∃ V : K → (Hilbert I →L[ℂ] Hilbert E), IsKrausRepresentation Psi.val V ∧
      ∀ k, operatorRank (V k) ≤
        operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi k)))) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
