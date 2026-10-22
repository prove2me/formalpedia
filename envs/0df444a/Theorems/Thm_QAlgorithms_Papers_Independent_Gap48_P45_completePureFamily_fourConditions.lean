-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_completePureFamily_fourConditions
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.completePureFamily_fourConditions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:55:21.527726+00:00
-- url     : https://prove2.me/theorems/aa3b47a5-a3a7-400e-8246-9921975e8432
-- title:
--   Theorem 4: complete pure-family classification, all four equivalent conditions
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. For vectors $\psi_p^k$ with $\sum_p\|\psi_p^k\|^2=1$ and $\langle\psi_t^k|\psi_p^k\rangle=0$ when $p\ne t$, define $N_{P,\psi}(X)=\sum_{k,l,p,t}P_kXP_l\otimes\langle\psi_t^l|\psi_p^k\rangle|p\rangle\langle t|$ on $H_A\otimes H_m$. Here $H_m$ has dimension $m$, including countable infinity. Let $S$ be a complete pure family, use its canonical component projections, put $m=m_1$, and define $\widehat S=\{\rho:\rho=\sum_kP_k\rho P_k\}$. For any fixed complement, the following four conditions are equivalent:
--
--   $$\Phi\text{ reversible on }S\iff\Phi\text{ reversible on }\widehat S\iff\widehat\Phi(X)=\sum_k\operatorname{Tr}(P_kX)\sigma_k,\ \operatorname{rank}\sigma_k\le m\iff\Phi\sim N_{P,\psi}.$$
--
--   The $\sigma_k$ are normalized states. Projections and $\widehat S$ are computed from $S$.
--
--   This result classifies complete pure-family reversibility through its canonical orthogonal components.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 15, Theorem 4: complete pure-family classification, all four equivalent conditions

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

/-- Theorem 4, PDF pp.15–16: all four conditions. Components, projections,
and the block-diagonal family are computed from S, not supplied as premises. -/
theorem completePureFamily_fourConditions
    {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (S : Set (State I)) (hPure : S ⊆ pureStates I) (hComplete : CompleteFamily S) :
    (ReversibleOn Phi.val S ↔ ReversibleOn Phi.val (blockDiagonalStates (componentProjection S))) ∧
    (ReversibleOn Phi.val S ↔ HasBlockCQForm Psi.val (componentProjection S) (rankMultiplicity Phi.val 1)) ∧
    (ReversibleOn Phi.val S ↔ HasBlockNormalForm Phi.val (componentProjection S) (rankMultiplicity Phi.val 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
