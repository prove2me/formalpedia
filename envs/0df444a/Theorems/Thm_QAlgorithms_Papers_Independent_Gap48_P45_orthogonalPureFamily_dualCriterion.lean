-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_orthogonalPureFamily_dualCriterion
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.orthogonalPureFamily_dualCriterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:49:30.688078+00:00
-- url     : https://prove2.me/theorems/b9845e69-4a77-4760-ab34-bfdebe697948
-- title:
--   Corollary 1: dual-channel test for orthogonal pure-state reversibility
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. Let $\{v_i\}$ be a specified orthonormal basis, $P_i=|v_i\rangle\langle v_i|$, and $m=m_1$. Then
--
--   $$\Phi\text{ reversible on }\{P_i\}\iff \exists W:H_A\otimes H_m\longrightarrow H_B\text{ partial isometry},\quad \Phi^*(W(P_i\otimes I)W^*)=P_i\quad\forall i.$$
--
--   This result tests exact recovery using bounded observables of the channel dual.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 12, Corollary 1: dual-channel test for orthogonal pure-state reversibility

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

/-- Corollary 1, PDF p.12(12): one partial isometry W before every i.
Neither unitarity nor surjectivity is imposed. -/
theorem orthogonalPureFamily_dualCriterion
    {I J L : Type} [Countable I] [Countable J] [Countable L] [Nonempty I] [Nonempty J]
    (Phi : Channel I J) (v : L → Hilbert I) (hBasis : OrthonormalBasisFamily v) :
    ReversibleOn Phi.val (vectorStates v) ↔
      ∃ W : Hilbert (I × BoundIndex (rankMultiplicity Phi.val 1)) →L[ℂ] Hilbert J,
        W.comp (W.adjoint.comp W) = W ∧ W.adjoint.comp (W.comp W.adjoint) = W.adjoint ∧
        ∀ i, boundedOperator (rankOne (v i)) =
          channelDual Phi.val (W.comp ((tensorIdentityEffect
            (M := BoundIndex (rankMultiplicity Phi.val 1))
            (boundedOperator (rankOne (v i)))).comp W.adjoint)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
