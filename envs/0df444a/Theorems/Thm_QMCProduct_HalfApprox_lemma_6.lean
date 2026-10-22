-- Prove2me | Theorems.Thm_QMCProduct_HalfApprox_lemma_6
-- name    : QMCProduct.HalfApprox.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:55.076989+00:00
-- url     : https://prove2.me/theorems/02994bef-910b-4673-8817-2387116bf3af
-- title:
--   Lemma 6, p. 18 — if h(v, γ) < 0 on (−1/3, γ] and g(γ) ≥ 1/2, then (1 + F(3, v))/(1 + 3v) ≥ 1/2 there
-- statement:
--   Let $F(3,v)=\frac{8}{3\pi}v\,{}_2F_1\left(\tfrac12,\tfrac12;\tfrac52;v^2\right)$ (equation (3) at $k=3$) and
--   $$h(v,\gamma)=\frac{8(3\gamma+1)\gamma^2\,{}_2F_1\left(\tfrac32,\tfrac32;\tfrac72;\gamma^2\right)+40\,{}_2F_1\left(\tfrac12,\tfrac12;\tfrac52;\gamma^2\right)-45\pi}{15\pi(3v+1)^2}.$$
--   Let $\gamma\in[1/3,1)$ be such that $h(v,\gamma)<0$ for all $v\in(-1/3,\gamma]$ and
--   $$\frac{1+F(3,\gamma)}{1+3\gamma}\ge\frac12.$$
--   Then
--   $$\frac{1+F(3,v)}{1+3v}\ge\frac12\qquad\text{for all }v\in(-1/3,\gamma].$$
--
--   The ratio $(1+F(3,v))/(1+3v)$ is the approximation factor of Gaussian product-state rounding on an edge with value $v$ (equation (7) against $\mu=(1+3v)/4$), so the lemma reduces a worst case over an interval to two checks at a single threshold.
--
--   **Formalization Note** The page's $\min_{v\in(-1/3,\gamma]}$ is stated as a lower bound at every point of the interval, which is the same statement whether or not the minimum is attained.
-- source:
--   Parekh & Thompson, An Optimal Product-State Approximation for 2-Local Quantum Hamiltonians with Positive Terms, arXiv:2206.08342v2, p. 18, Lemma 6

import Definitions.Def_QMCProduct_HalfApprox_Algorithm

set_option autoImplicit false

namespace QMCProduct.HalfApprox

/-- Lemma 6, p. 18. The minimum over `(-1/3, γ]` is stated as a pointwise lower bound. -/
theorem lemma_6 (γ : ℝ) (hγ1 : 1 / 3 ≤ γ) (hγ2 : γ < 1)
    (hh : ∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) γ, hLemma6 v γ < 0)
    (hg : (1 / 2 : ℝ) ≤ (1 + F 3 γ) / (1 + 3 * γ)) :
    ∀ v ∈ Set.Ioc (-(1 / 3 : ℝ)) γ, (1 / 2 : ℝ) ≤ (1 + F 3 v) / (1 + 3 * v) := by sorry

end QMCProduct.HalfApprox
