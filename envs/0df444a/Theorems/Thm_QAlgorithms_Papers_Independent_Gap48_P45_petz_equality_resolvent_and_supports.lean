-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P45_petz_equality_resolvent_and_supports
-- name    : QAlgorithms.Papers.Independent.Gap48.P45.petz_equality_resolvent_and_supports
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-26T00:32:18.040786+00:00
-- url     : https://prove2.me/theorems/e44d0fa4-04fe-46a5-95d4-8681ae6691ae
-- title:
--   Equal relative entropies force equal resolvent sums and support inclusions
-- statement:
--   Let $\rho=\sum_i r_i|e_i\rangle\langle e_i|$, $\sigma=\sum_j s_j|f_j\rangle\langle f_j|$ and the same for $\Phi(\rho),\Phi(\sigma)$ with $r^0,s^0,e^0,f^0$. If $D(\rho\|\sigma)<\infty$ and $D(\Phi(\rho)\|\Phi(\sigma))=D(\rho\|\sigma)$, then for every $t>0$
--
--   $$\sum_{j,i}\frac{|\langle f^0_j,e^0_i\rangle|^2 (r^0_i)^2}{s^0_j+t r^0_i}=\sum_{j,i}\frac{|\langle f_j,e_i\rangle|^2 r_i^2}{s_j+t r_i},$$
--
--   and $\langle f_j,e_i\rangle=0$ whenever $s_j=0<r_i$ (likewise on the output side).
--
--   Role: First step of the equality case: converts equality of relative entropies into equality of the resolvent values for every $t>0$.
-- source:
--   M. E. Shirokov, Reversibility conditions for quantum channels and their applications, https://arxiv.org/abs/1203.0262, Theorem 1, proof of the equality case (PDF pp. 6-7) and Appendix 5.1 (pp. 23-25); D. Petz, Monotonicity of quantum relative entropy revisited, Rev. Math. Phys. 15 (2003) 79-91, integral representation of the logarithm

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

theorem petz_equality_resolvent_and_supports
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
    (heq : extendedRelativeEntropyNats (Phi.val rho.coefficients) (Phi.val sigma.coefficients) =
      extendedRelativeEntropyNats rho.coefficients sigma.coefficients) :
    (∀ t : ℝ, 0 < t →
      ∑' p : κ0 × ι0, ‖inner ℂ (f0 p.1) (e0 p.2)‖ ^ 2 * r0 p.2 ^ 2 / (s0 p.1 + t * r0 p.2) =
        ∑' p : κ × ι, ‖inner ℂ (f p.1) (e p.2)‖ ^ 2 * r p.2 ^ 2 / (s p.1 + t * r p.2)) ∧
    (∀ j i, s j = 0 → 0 < r i → inner ℂ (f j) (e i) = 0) ∧
    (∀ j i, s0 j = 0 → 0 < r0 i → inner ℂ (f0 j) (e0 i) = 0) := by sorry

end QAlgorithms.Papers.Independent.Gap48.P45
