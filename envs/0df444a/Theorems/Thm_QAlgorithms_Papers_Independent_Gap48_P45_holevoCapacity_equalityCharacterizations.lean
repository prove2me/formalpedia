-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_holevoCapacity_equalityCharacterizations
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.holevoCapacity_equalityCharacterizations
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T06:05:21.468994+00:00
-- url     : https://prove2.me/theorems/0cf6049c-2fcf-4524-af98-80f78c447df7
-- title:
--   Corollary 4: both equality characterizations of the capacity bound
-- statement:
--   All physical Hilbert spaces are nonzero complex separable Hilbert spaces, with finite dimensions included. States are positive trace-class operators of trace one, channels are completely positive and trace preserving on the entire trace class, and logarithms are natural. Inner products are conjugate-linear in the first argument. Write $H_B^\Phi$ for the closed span of all output supports, $d_\Phi=\dim H_B^\Phi$, $m_0(\Phi)=\dim\ker(\Phi^*|_{\mathcal B(H_B^\Phi)})$, and $m_r=\min\{m_0(\Phi)+r^2,d_\Phi\}$; dimensions retain infinity. For vectors $\psi_p^k$ with $\sum_p\|\psi_p^k\|^2=1$ and $\langle\psi_t^k|\psi_p^k\rangle=0$ when $p\ne t$, define $N_{P,\psi}(X)=\sum_{k,l,p,t}P_kXP_l\otimes\langle\psi_t^l|\psi_p^k\rangle|p\rangle\langle t|$ on $H_A\otimes H_m$. Here $H_m$ has dimension $m$, including countable infinity. For unit vectors $\eta_k$, write $G_{P,\eta}(X)=\sum_{k,l}\langle\eta_l|\eta_k\rangle P_kXP_l$. For a channel between positive finite-dimensional spaces:
--
--   $$\bar C(\Phi)=\ln\dim H_A\iff\exists\text{ nonzero orthogonal resolution }\{P_k\}\text{ with all four classification properties below}.$$
--
--   These properties are: one recovery for all pure states within individual blocks; one recovery for all block-diagonal states; the complementary form $\widehat\Phi(X)=\sum_k\operatorname{Tr}(P_kX)\sigma_k$ with states of rank at most $m_1$; and isometrical equivalence to $N_{P,\psi}$ with $m=m_1$. If $H_B=H_A$, there is also the characterization
--
--   $$\bar C(\Phi)=\ln\dim H_A\iff\Phi\text{ is unitarily equivalent to some }G_{P,\eta}.$$
--
--   All output vectors and states, the resolution, and the common recovery maps are existential conclusions.
--
--   This result characterizes both general and equal-space equality cases of the dimension bound.
-- source:
--   Reversibility conditions for quantum channels and their applications, arXiv:1203.0262v3, PDF p. 21, Corollary 4: both equality characterizations of the capacity bound

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

/-- Corollary 4, PDF p.21, BOTH A and B. A expands all four explicit channel
forms; B specializes to the same input and output Hilbert space. -/
theorem holevoCapacity_equalityCharacterizations
    {I : Type} [Fintype I] [Nonempty I] :
    (∀ (J E : Type) [Fintype J] [Nonempty J] [Countable E] [Nonempty E]
        (Phi : Channel I J) (Psi : Channel I E), Complementary Phi Psi →
      ((finiteEnsembleCapacity Phi.val Set.univ) = ENNReal.ofReal (Real.log (Fintype.card I : ℝ)) ↔
        ∃ (K : Type) (_ : Countable K) (P : K → (Hilbert I →L[ℂ] Hilbert I)),
          OrthogonalResolution P ∧ ResolutionClassification Phi.val Psi.val P)) ∧
    (∀ Phi : Channel I I,
      (finiteEnsembleCapacity Phi.val Set.univ) = ENNReal.ofReal (Real.log (Fintype.card I : ℝ)) ↔
        ∃ (K : Type) (_ : Countable K) (P : K → (Hilbert I →L[ℂ] Hilbert I)),
          OrthogonalResolution P ∧ HasGramNormalForm Phi.val P False) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45

end
