-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_positiveOperator_dualRankDecomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.positiveOperator_dualRankDecomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:46:55.983499+00:00
-- url     : https://prove2.me/theorems/45897c41-9a5a-461a-a3d3-de2218464383
-- title:
--   Lemma 2: positive operator decomposition controlled by dual rank
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Let $B\ge0$ be any bounded output operator, and suppose $\operatorname{rank}\Phi^*(B)=r<\infty$. Set $m=\min\{\dim\ker\Phi^*+r^2,\dim H_B\}$. There exist vectors $\psi_j\in H_B$, allowing zero vectors, such that
--
--   $$B=\sum_{j=1}^m|\psi_j\rangle\langle\psi_j|.$$
--
--   This result controls a positive operator decomposition using the dimension lost by the channel dual.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 10, Lemma 2: positive operator decomposition controlled by dual rank

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

/-- Lemma 2, PDF pp.10–11. B is bounded positive, not necessarily trace class.
The unrestricted dual kernel contributes at r=0; infinite sums are strong. -/
theorem positiveOperator_dualRankDecomposition
    {I J : Type} [Countable I] [Countable J] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (B : Hilbert J →L[ℂ] Hilbert J)
    (hPositive : B.adjoint = B ∧ ∀ x, 0 ≤ (inner ℂ x (B x)).re)
    (r : ℕ) (hRank : operatorRank (channelDual Phi.val B) = r) :
    let m : ℕ∞ := min
      (Cardinal.toENat (Module.rank ℂ (Submodule.span ℂ
        {C : Hilbert J →L[ℂ] Hilbert J | channelDual Phi.val C = 0})) + (r : ℕ∞) ^ 2)
      (dimensionCount J)
    ∃ psi : BoundIndex m → Hilbert J, ∀ x : Hilbert J,
      HasSum (fun j => boundedOperator (rankOne (psi j)) x) (B x) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
