-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_orthogonalPureFamily_threeConditions
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.orthogonalPureFamily_threeConditions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T05:48:22.426557+00:00
-- url     : https://prove2.me/theorems/01385ea0-22dd-4454-8997-5d6fce8d3e60
-- title:
--   Proposition 1: orthogonal pure-state reversibility, all three equivalent conditions
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. For vectors $\psi_p^k$ with $\sum_p\|\psi_p^k\|^2=1$ and $\langle\psi_t^k|\psi_p^k\rangle=0$ when $p\ne t$, define $N_{P,\psi}(X)=\sum_{k,l,p,t}P_kXP_l\otimes\langle\psi_t^l|\psi_p^k\rangle|p\rangle\langle t|$ on $H_A\otimes H_m$. Here $H_m$ has dimension $m$, including countable infinity. Let $\{v_i\}$ be a specified orthonormal basis, set $P_i=|v_i\rangle\langle v_i|$, and let $\widehat\Phi$ be any complement of $\Phi$. The following are equivalent:
--
--   $$\Phi\text{ reversible on }\{|v_i\rangle\langle v_i|\}\iff\widehat\Phi(X)=\sum_i\langle v_i|X|v_i\rangle\sigma_i,\ \operatorname{rank}\sigma_i\le m_1\iff\Phi\sim N_{P,\psi},$$
--
--   where each $\sigma_i$ is a state and $\sim$ denotes isometrical equivalence via one partial isometry satisfying both conjugation identities on all trace-class inputs.
--
--   This result classifies the channels that recover a specified orthonormal pure-state family.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 11, Proposition 1: orthogonal pure-state reversibility, all three equivalent conditions

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

/-- Proposition 1, PDF pp.11–12: all three conditions for the specified ONB,
including the rank bound and the Gram-indexed channel into H_A tensor H_m. -/
theorem orthogonalPureFamily_threeConditions
    {I J E L : Type} [Countable I] [Countable J] [Countable E] [Countable L]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (v : L → Hilbert I) (hBasis : OrthonormalBasisFamily v) :
    (ReversibleOn Phi.val (vectorStates v) ↔
      HasBlockCQForm Psi.val (fun i => boundedOperator (rankOne (v i))) (rankMultiplicity Phi.val 1)) ∧
    (ReversibleOn Phi.val (vectorStates v) ↔
      HasBlockNormalForm Phi.val (fun i => boundedOperator (rankOne (v i))) (rankMultiplicity Phi.val 1)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
