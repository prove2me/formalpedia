-- Prove2me | Theorems.Thm_SDCA_AlmostSmooth_proposition_1
-- name    : SDCA.AlmostSmooth.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T19:06:20.356994+00:00
-- url     : https://prove2.me/theorems/4c4cc55c-eafd-495f-8947-97075147b1f7
-- title:
--   Proposition 1 — refined dual strong convexity (4) gives inequality (5), and $|(w^*-w)^\top x_i|\ge\gamma_i|a_i-\alpha_i^*|$ (6)
-- statement:
--   Let $x_1,\dots,x_n\in\mathbb R^d$, let $\varphi_1,\dots,\varphi_n:\mathbb R\to\mathbb R$, and let $\lambda>0$. Suppose functions $\gamma_i(\cdot)\ge0$ satisfy the refined dual strong convexity condition (4): for all $a,b\in\mathbb R$ and every $u\in\partial\varphi_i^*(-b)$, $\varphi_i^*(-a)-\varphi_i^*(-b)+u(a-b)\ge\gamma_i(u)|a-b|^2$. Let $\alpha^*\in\mathbb R^n$, put $w^*=w(\alpha^*)=\frac{1}{\lambda n}\sum_i\alpha_i^*x_i$, and assume the first-order fact $-\alpha_i^*\in\partial\varphi_i(w^{*\top}x_i)$ for every $i$. Let $\gamma_i=\gamma_i(w^{*\top}x_i)$. Then:
--
--   1. For every feasible dual variable $\alpha$ and $w=w(\alpha)$,
--   $$
--   D(\alpha^*)-D(\alpha)\ge\frac1n\sum_{i=1}^n\gamma_i|\alpha_i-\alpha_i^*|^2+\frac\lambda2(w-w^*)^\top(w-w^*). \tag{5}
--   $$
--   2. For every $w\in\mathbb R^d$, every $i$ and every $a_i$ with $-a_i\in\partial\varphi_i(w^\top x_i)$,
--   $$
--   |(w^*-w)^\top x_i|\ge\gamma_i|a_i-\alpha_i^*|. \tag{6}
--   $$
--
--   Inequality (5) is a strong concavity of the dual objective around $\alpha^*$ whose modulus varies by coordinate; it is the hypothesis of Lemma 5 and Theorem 5.
--
--   **Formalization Note** The paper takes $\alpha^*$ to be a dual optimum and uses the facts of p. 12, $-\alpha_i^*\in\partial\varphi_i(w^{*\top}x_i)$ and $w^*=\frac{1}{\lambda n}\sum_i\alpha_i^*x_i$; only these facts enter the proof, so they are the hypotheses and optimality of $\alpha^*$ is not assumed. The conjugate-side fact $w^{*\top}x_i\in\partial\varphi_i^*(-\alpha_i^*)$ follows from the stated one. Inequality (5) is the `EReal` predicate of the definition file. Convexity of the losses is not needed and not assumed.
-- source:
--   Shalev-Shwartz and Zhang, Stochastic Dual Coordinate Ascent Methods for Regularized Loss Minimization, arXiv:1209.1873v2, pp. 8–9, Proposition 1, (5) and (6); proof §7.5, p. 18; facts of §7, p. 12

import Mathlib
import Definitions.Def_SDCA_AlmostSmooth_Model

open scoped InnerProductSpace

namespace SDCA.AlmostSmooth

/-- Proposition 1 (pp. 8–9; proof §7.5, p. 18). Under (4), with `γᵢ = γᵢ(w*ᵀxᵢ)` and
`w* = w(α*)` satisfying the p. 12 fact `−α*ᵢ ∈ ∂φᵢ(w*ᵀxᵢ)`:
(5) `D(α*) − D(α) ≥ (1/n) ∑ᵢ γᵢ|αᵢ − α*ᵢ|² + (λ/2)‖w(α) − w*‖²` for every feasible `α`; and
(6) for every `w` and `aᵢ` with `−aᵢ ∈ ∂φᵢ(wᵀxᵢ)`, `|(w* − w)ᵀxᵢ| ≥ γᵢ|aᵢ − α*ᵢ|`. -/
theorem proposition_1 {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (γfun : Fin n → ℝ → ℝ)
    (h4 : RefinedDualStrongConvexity φ γfun) (αstar : Fin n → ℝ)
    (hstar : ∀ i, IsSubgrad (φ i) ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ (-αstar i)) :
    DualStrongConvexity lam x φ (fun i => γfun i ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ) αstar ∧
      ∀ (w : EuclideanSpace ℝ (Fin d)) (i : Fin n) (a : ℝ), IsSubgrad (φ i) ⟪w, x i⟫_ℝ (-a) →
        γfun i ⟪SDCA.Smooth.wOf lam x αstar, x i⟫_ℝ * |a - αstar i| ≤ |⟪SDCA.Smooth.wOf lam x αstar - w, x i⟫_ℝ| := by sorry

end SDCA.AlmostSmooth
