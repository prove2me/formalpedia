-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P46_gaussianRandomOptimizer
-- name    : QAlgorithms.Papers.Independent.Renew46.P46.gaussianRandomOptimizer
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T21:57:54.100019+00:00
-- url     : https://prove2.me/theorems/37279c52-434a-422f-99ea-818de39e6fcf
-- title:
--   §V: Gaussian random-exponent optimization, capacity derivative, and (45)
-- statement:
--   Fix energy $E>0$ and the Gaussian prior $G_E$ of the noiseless coherent channel. Write $\mu_E(s,p)$ for its actual random exponent functional, with $0\le s\le1$ and $0\le p<1/E$. For each such $s$ a maximizing $p$ exists and satisfies
--
--   $$(1+E-pE)^s(1-p)=E^s.$$
--
--   At $s=0$ the unique optimizer is $p=0$, and $\partial_s\mu_E(0,0)=h(E)$, where $h(E)=(E+1)\log(E+1)-E\log E$. Put $q(E)=(1+\sqrt{1+4E^2})/2$. At $s=1$ the stationary equation and the maximum have the unique solution $p_1=1+1/E-q(E)/E\in[0,1/E)$, and
--
--   $$\mu_E(1,p_1)=A(E)=2(E+1-q(E))+\log q(E),$$
--   $$\partial_s\mu_E(1,p_1)=B(E)=E+1-q(E)+\frac{q(E)^2\log q(E)-E^2\log E}{q(E)^2-E^2}.$$
--
--   The derivatives hold $p$ fixed. The symbol $q$ distinguishes the source's algebraic root from the thermal entropy.
-- source:
--   On Quantum Communication Channels with Constrained Inputs, arXiv:quant-ph/9705054v1, PDF p. 14, §V: Gaussian random-exponent optimization, capacity derivative, and (45)

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P46

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P46

open Filter MeasureTheory QAlgorithms.RealRegisters

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

/-- Section V, PDF pp.13-14, (44)-(45): optimization with Gaussian prior fixed.
Derivatives in s hold p fixed. q is the source's algebraic g, not entropy h. -/
theorem gaussianRandomOptimizer (E : ℝ) (hE : 0 < E) :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∃ p : ℝ,
      0 ≤ p ∧ p < 1 / E ∧
      (1 + E - p * E) ^ s * (1 - p) = E ^ s ∧
      (∀ t : ℝ, 0 ≤ t → t < 1 / E → gaussianMu E s t ≤ gaussianMu E s p)) ∧
    (∀ p : ℝ, 0 ≤ p → p < 1 / E →
      (gaussianMu E 0 p ≤ gaussianMu E 0 0 ∧
        (gaussianMu E 0 p = gaussianMu E 0 0 ↔ p = 0))) ∧
    HasDerivAt (fun s => gaussianMu E s 0) (h E) 0 ∧
    0 ≤ bestP E 1 ∧ bestP E 1 < 1 / E ∧
    (∀ p : ℝ, 0 ≤ p → p < 1 / E →
      ((1 + E - p * E) * (1 - p) = E ↔ p = bestP E 1) ∧
      gaussianMu E 1 p ≤ gaussianMu E 1 (bestP E 1) ∧
      (gaussianMu E 1 p = gaussianMu E 1 (bestP E 1) ↔ p = bestP E 1)) ∧
    gaussianMu E 1 (bestP E 1) = Avalue E ∧
    HasDerivAt (fun s => gaussianMu E s (bestP E 1)) (Bvalue E) 1 := by sorry

end QAlgorithms.Papers.Independent.Renew46.P46

end
