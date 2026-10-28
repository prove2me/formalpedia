-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_dual_rank_rankOne_resolution
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.dual_rank_rankOne_resolution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:03:25.511874+00:00
-- url     : https://prove2.me/theorems/9ac851c4-e7e3-4916-b952-7d298c8dc1ad
-- title:
--   Lemma 2: rank-one resolution of an output-supported positive operator
-- statement:
--   Let $\Phi,\Psi$ be complementary channels, $P$ the projection onto the output space of $\Phi$, and $B\ge 0$ a bounded operator with $PBP=B$ and $\operatorname{rank}\Phi^*(B)\le r$. Then there are at most $m_r=\operatorname{rankMultiplicity}(\Phi,r)$ vectors $\psi_j$ with
--
--   $$\langle x,Bx\rangle=\sum_j|\langle\psi_j,x\rangle|^2\quad(x\in\mathcal H_J),\qquad \operatorname{rank}\Phi^*(|\psi_j\rangle\langle\psi_j|)\le r .$$
--
--   Role: splits each output operator $B_i$ into rank-one pieces whose dual images keep rank at most $r$; these pieces index the Kraus operators of the complementary channel.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Lemma 2 (PDF p. 10), in the restricted form used in the proof of Theorem 3 (B supported on the output space of Phi)

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

theorem dual_rank_rankOne_resolution {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (B : Hilbert J →L[ℂ] Hilbert J)
    (hB : ContinuousLinearMap.adjoint B = B ∧ ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (hsupp : (outputProjection Phi.val).comp (B.comp (outputProjection Phi.val)) = B)
    (r : ℕ) (hr : operatorRank (channelDual Phi.val B) ≤ r) :
    ∃ psi : BoundIndex (rankMultiplicity Phi.val r) → Hilbert J,
      (∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B x)).re) ∧
      ∀ j, operatorRank (channelDual Phi.val (boundedOperator (rankOne (psi j)))) ≤ r := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
