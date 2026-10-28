-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_complement_kraus_rankOne_of_output_resolution
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.complement_kraus_rankOne_of_output_resolution
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-27T11:05:48.384473+00:00
-- url     : https://prove2.me/theorems/d60b52c3-d34a-4a77-8b6f-406ab0888e47
-- title:
--   Rank-one Kraus operators of the complement from a rank-one dual resolution
-- statement:
--   Let $\Phi,\Psi$ be complementary channels, $P$ the projection onto the output space of $\Phi$, and $(B_i)_{i\in L}$ bounded operators with $\sum_i\langle x,B_ix\rangle=\langle x,Px\rangle$. Suppose each $B_i$ has a rank-one resolution $\langle x,B_ix\rangle=\sum_{j}|\langle\psi_{ij},x\rangle|^2$ indexed by $m_1=\operatorname{rankMultiplicity}(\Phi,1)$, and $\Phi^*(B_i)=|w_i\rangle\langle w_i|$ with $w_i\ne0$. Then there are vectors $\varphi_{ij}$ with $\sum_j\|\varphi_{ij}\|^2=1$ such that
--
--   $$\Psi(\rho)=\sum_{i,j}|\varphi_{ij}\rangle\langle w_i|\,\rho\,|w_i\rangle\langle\varphi_{ij}| ,$$
--
--   i.e. the operators $|\varphi_{ij}\rangle\langle w_i|$ form a Kraus representation of $\Psi$.
--
--   Role: gives the rank-one Kraus form of the complementary channel in the pure-state clause.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, proof of Theorem 3, case r = 1 (PDF pp. 8-9: Kraus operators of the complementary channel built from the resolution of the output support, Lemma 2 with r = 1)

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

theorem complement_kraus_rankOne_of_output_resolution {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (B : L → (Hilbert J →L[ℂ] Hilbert J))
    (hres : ∀ x, HasSum (fun i => (inner ℂ x (B i x)).re)
      (inner ℂ x (outputProjection Phi.val x)).re)
    (hpsi0 : ∀ i, ∃ psi : BoundIndex (rankMultiplicity Phi.val 1) → Hilbert J,
      ∀ x, HasSum (fun j => ‖inner ℂ (psi j) x‖ ^ 2) (inner ℂ x (B i x)).re)
    (w : L → Hilbert I) (hw0 : ∀ i, w i ≠ 0)
    (hdual : ∀ i, channelDual Phi.val (B i) = (innerSL ℂ (w i)).smulRight (w i)) :
    ∃ phi : L → BoundIndex (rankMultiplicity Phi.val 1) → Hilbert E,
      (∀ i, HasSum (fun j => ‖phi i j‖ ^ 2) 1) ∧
      IsKrausRepresentation Psi.val
        (fun p : L × BoundIndex (rankMultiplicity Phi.val 1) =>
          ((innerSL ℂ (w p.1)).smulRight (phi p.1 p.2) : Hilbert I →L[ℂ] Hilbert E)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
