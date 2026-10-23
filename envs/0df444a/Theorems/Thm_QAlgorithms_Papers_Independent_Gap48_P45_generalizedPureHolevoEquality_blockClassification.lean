-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_generalizedPureHolevoEquality_blockClassification
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.generalizedPureHolevoEquality_blockClassification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:03:00.679634+00:00
-- url     : https://prove2.me/theorems/223417ab-3a70-4b0c-82cc-f1e85c1ea4a6
-- title:
--   Theorem 5: unambiguous pure-ensemble block classification
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. An OND family admits no partition into two nonempty mutually orthogonal subfamilies. Its components are obtained by finite chains of nonorthogonal pure states, and $P_k$ projects onto the closed span of component $k$. For vectors $\psi_p^k$ with $\sum_p\|\psi_p^k\|^2=1$ and $\langle\psi_t^k|\psi_p^k\rangle=0$ when $p\ne t$, define $N_{P,\psi}(X)=\sum_{k,l,p,t}P_kXP_l\otimes\langle\psi_t^l|\psi_p^k\rangle|p\rangle\langle t|$ on $H_A\otimes H_m$. Here $H_m$ has dimension $m$, including countable infinity. Let $\mu$ be a Borel ensemble concentrated on pure states, with faithful average and preserved finite Holevo quantity. Let $S=\operatorname{supp}\mu$ and use its canonical OND projections $P_k$, with $m=m_1$. They form a countable nonzero orthogonal resolution, and all four classification conditions hold:
--
--   $$\Phi\text{ reversible on }S,\quad\Phi\text{ reversible on }\widehat S,\quad\widehat\Phi(X)=\sum_k\operatorname{Tr}(P_kX)\sigma_k,\ \operatorname{rank}\sigma_k\le m,\quad\Phi\sim N_{P,\psi}.$$
--
--   Here $\widehat S=\{\rho:\rho=\sum_kP_k\rho P_k\}$, each $\sigma_k$ is a state, and $\mu(\widehat S)=1$. The computed resolution is the finest nonzero one with this almost-everywhere block property.
--
--   This result translates preserved pure-ensemble information into the full block classification.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 20, Theorem 5: unambiguous pure-ensemble block classification

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

/-- Theorem 5 pure-state clause, PDF p.20 n.11: all four classification clauses
and almost-everywhere pinching. The finest nonzero resolution is computed from
OND components of the pure support, not chosen as the vacuous one-block resolution. -/
theorem generalizedPureHolevoEquality_blockClassification
    {I J E : Type} [Countable I] [Countable J] [Countable E]
    [Nonempty I] [Nonempty J] [Nonempty E]
    (Phi : Channel I J) (Psi : Channel I E) (hComp : Complementary Phi Psi)
    (mu : GeneralizedEnsemble I)
    (hPure : ∀ᵐ rho ∂(mu : Measure (State I)), rho ∈ pureStates I)
    (hFullRank : FullRank (averageCoefficients mu))
    (hFinite : ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu < ⊤)
    (hEquality : ensembleHolevo Phi.val mu = ensembleHolevo (id : Matrix I I ℂ → Matrix I I ℂ) mu) :
    let S := (mu : Measure (State I)).support
    (componentSets S).Countable ∧ OrthogonalResolution (componentProjection S) ∧
      ReversibleOn Phi.val S ∧ ReversibleOn Phi.val (blockDiagonalStates (componentProjection S)) ∧
      HasBlockCQForm Psi.val (componentProjection S) (rankMultiplicity Phi.val 1) ∧
      HasBlockNormalForm Phi.val (componentProjection S) (rankMultiplicity Phi.val 1) ∧
      (∀ᵐ rho ∂(mu : Measure (State I)), rho ∈ blockDiagonalStates (componentProjection S)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
