-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_matrix_entries
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_matrix_entries
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:34:32.546636+00:00
-- url     : https://prove2.me/theorems/df55710f-7a71-42ea-886b-e54b7b44dbbe
-- title:
--   Approximate intertwiners give the Petz formula on matrix entries
-- statement:
--   Under the eigen-data of $\rho,\sigma,\Phi(\rho),\Phi(\sigma)$ and the approximation property of the previous step, for $t=\Phi(\sigma)^{1/2}$, $q=\sigma^{1/2}$ and any bounded $B$ with $tBt=\Phi(|qu\rangle\langle qv|)$,
--
--   $$\sum_i r^0_i\langle e^0_i,B e^0_i\rangle=\sum_i r_i\langle e_i,(|u\rangle\langle v|)e_i\rangle .$$
--
--   Role: Last step of the equality case: identifies each matrix entry of $\Theta_\sigma(\Phi(\rho))$ with that of $\rho$.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Theorem 1, proof of the equality case (PDF pp. 6-7) and Appendix 5.1 (pp. 23-25), the Petz formula $\rho=\Theta_\sigma(\Phi(\rho))$

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

theorem petz_equality_matrix_entries
    {I J : Type} [Countable I] [Countable J]
    (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr : HasSum r 1)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr' : HasSum r0 1)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (happ : ∀ ε : ℝ, 0 < ε → ∃ Z : Hilbert J →L[ℂ] Hilbert J,
      (∑' p : κ0 × ι0, ‖(Real.sqrt (s0 p.1) : ℂ) * inner ℂ (f0 p.1) (Z (e0 p.2)) -
          inner ℂ (f0 p.1) (e0 p.2) * (Real.sqrt (r0 p.2) : ℂ)‖ ^ 2) +
      (∑' p : κ × ι, ‖(Real.sqrt (s p.1) : ℂ) * inner ℂ (f p.1) (channelDual Phi.val Z (e p.2)) -
          inner ℂ (f p.1) (e p.2) * (Real.sqrt (r p.2) : ℂ)‖ ^ 2) < ε)
    (t : Hilbert J →L[ℂ] Hilbert J) (ht : ContinuousLinearMap.adjoint t = t)
    (htf : ∀ j, t (f0 j) = ((Real.sqrt (s0 j) : ℝ) : ℂ) • f0 j)
    (sq : Hilbert I →L[ℂ] Hilbert I) (hsq : ContinuousLinearMap.adjoint sq = sq)
    (hsqf : ∀ j, sq (f j) = ((Real.sqrt (s j) : ℝ) : ℂ) • f j)
    (u v : Hilbert I) (B : Hilbert J →L[ℂ] Hilbert J)
    (hB : t.comp (B.comp t) =
      boundedOperator (Phi.val (operatorCoeff ((innerSL ℂ (sq v)).smulRight (sq u))))) :
    ∑' i, (r0 i : ℂ) * inner ℂ (e0 i) (B (e0 i)) =
      ∑' i, (r i : ℂ) * inner ℂ (e i) ((innerSL ℂ v).smulRight u (e i)) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
