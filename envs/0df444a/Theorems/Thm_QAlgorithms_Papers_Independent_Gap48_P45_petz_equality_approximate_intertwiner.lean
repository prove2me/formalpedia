-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_approximate_intertwiner
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_approximate_intertwiner
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:33:08.245411+00:00
-- url     : https://prove2.me/theorems/6f81a604-0d3d-4399-a8b8-fe84a7e62e7f
-- title:
--   Equal resolvent sums give approximate Petz intertwiners
-- statement:
--   Under the eigen-data of $\rho,\sigma,\Phi(\rho),\Phi(\sigma)$, if $D(\rho\|\sigma)<\infty$, the resolvent sums agree for every $t>0$, and the supports are compatible, then for every $\varepsilon>0$ there is a bounded $Z$ with
--
--   $$\sum_{j,i}\big|\sqrt{s^0_j}\langle f^0_j,Z e^0_i\rangle-\langle f^0_j,e^0_i\rangle\sqrt{r^0_i}\big|^2+\sum_{j,i}\big|\sqrt{s_j}\langle f_j,\Phi^*(Z) e_i\rangle-\langle f_j,e_i\rangle\sqrt{r_i}\big|^2<\varepsilon.$$
--
--   Role: Middle step of the equality case: $\rho^{1/2}$ lies in the closure of the operators $Z\mapsto(\sigma_0^{1/2}Z,\sigma^{1/2}\Phi^*(Z))$.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Theorem 1, proof of the equality case (PDF pp. 6-7) and Appendix 5.1 (pp. 23-25); D. Petz, Rev. Math. Phys. 15 (2003) 79-91, the resolvent identity in the proof of the equality case

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

theorem petz_equality_approximate_intertwiner
    {I J : Type} [Countable I] [Countable J]
    (Phi : Channel I J) (rho sigma : State I)
    {ι κ ι0 κ0 : Type} (e : HilbertBasis ι ℂ (Hilbert I)) (f : HilbertBasis κ ℂ (Hilbert I))
    (r : ι → ℝ) (s : κ → ℝ)
    (hr0 : ∀ i, 0 ≤ r i) (hr1 : Summable r)
    (hev : ∀ i, boundedOperator rho.coefficients (e i) = (r i : ℂ) • e i)
    (hs0 : ∀ j, 0 ≤ s j) (hs1 : Summable s)
    (hfv : ∀ j, boundedOperator sigma.coefficients (f j) = (s j : ℂ) • f j)
    (e0 : HilbertBasis ι0 ℂ (Hilbert J)) (f0 : HilbertBasis κ0 ℂ (Hilbert J))
    (r0 : ι0 → ℝ) (s0 : κ0 → ℝ)
    (hr0' : ∀ i, 0 ≤ r0 i) (hr1' : Summable r0)
    (hev' : ∀ i, boundedOperator (Phi.val rho.coefficients) (e0 i) = (r0 i : ℂ) • e0 i)
    (hs0' : ∀ j, 0 ≤ s0 j) (hs1' : Summable s0)
    (hfv' : ∀ j, boundedOperator (Phi.val sigma.coefficients) (f0 j) = (s0 j : ℂ) • f0 j)
    (hD : extendedRelativeEntropyNats rho.coefficients sigma.coefficients < ⊤)
    (heq : ∀ t : ℝ, 0 < t →
      ∑' p : κ0 × ι0, ‖inner ℂ (f0 p.1) (e0 p.2)‖ ^ 2 * r0 p.2 ^ 2 / (s0 p.1 + t * r0 p.2) =
        ∑' p : κ × ι, ‖inner ℂ (f p.1) (e p.2)‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2))
    (hsupp : ∀ j i, s j = 0 → 0 < r i → inner ℂ (f j) (e i) = 0)
    (hsupp' : ∀ j i, s0 j = 0 → 0 < r0 i → inner ℂ (f0 j) (e0 i) = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ Z : Hilbert J →L[ℂ] Hilbert J,
      (∑' p : κ0 × ι0, ‖(Real.sqrt (s0 p.1) : ℂ) * inner ℂ (f0 p.1) (Z (e0 p.2)) -
          inner ℂ (f0 p.1) (e0 p.2) * (Real.sqrt (r0 p.2) : ℂ)‖ ^ 2) +
      (∑' p : κ × ι, ‖(Real.sqrt (s p.1) : ℂ) * inner ℂ (f p.1) (channelDual Phi.val Z (e p.2)) -
          inner ℂ (f p.1) (e p.2) * (Real.sqrt (r p.2) : ℂ)‖ ^ 2) < ε := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
