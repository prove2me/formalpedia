-- Prove2me | Theorems.Thm_ShortWDRODual_Legendre_lemma_3
-- name    : ShortWDRODual.Legendre.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:35.040122+00:00
-- url     : https://prove2.me/theorems/88955308-9c55-4163-a0f4-873cd96a08dd
-- title:
--   Lemma 3, p. 13 — for decreasing convex h ≢ +∞ with h = +∞ on (−∞, 0), λ ↦ h*(−λ) is lsc, decreasing, convex, +∞ on λ < 0, h* ≢ +∞
-- statement:
--   Let $h:\mathbb R\to\mathbb R\cup\{+\infty\}$ be a monotonically decreasing convex function with $h(\rho)=+\infty$ for $\rho<0$ and $h\not\equiv+\infty$. Let $h^*(\lambda)=\sup_{\rho\in\mathbb R}\{\lambda\rho-h(\rho)\}$ be its Legendre transform. Then the function
--   $$\lambda\longmapsto h^*(-\lambda)=\sup_{\rho\in\mathbb R}\{-\lambda\rho-h(\rho)\}$$
--   is lower semi-continuous, monotonically decreasing and convex on $\mathbb R$, satisfies $h^*(-\lambda)=+\infty$ for $\lambda<0$, and $h^*\not\equiv+\infty$.
--
--   This is the one-dimensional convex-analysis fact used in the proof of Theorem 1, applied to $h=-\mathcal L$.
--
--   **Formalization Note** The paper calls the function $f$; it is renamed $h$ to avoid a clash with the loss. Values are in `EReal` with $h\ne-\infty$; convexity is the inequality $h((1-t)a+tb)\le(1-t)h(a)+t\,h(b)$ for $t\in[0,1]$ with real weights, where Mathlib's $0\cdot\infty=0$ is the intended convention for a weight $0$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Lemma 3, p. 13 (PDF p. 13); proof in EC.1, p. ec1 (PDF p. 15)

import Mathlib
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.Legendre

theorem lemma_3 (h : ℝ → EReal)
    (h_nbot : ∀ ρ, h ρ ≠ ⊥)
    (h_anti : Antitone h)
    (h_conv : ∀ a b t : ℝ, 0 ≤ t → t ≤ 1 →
      h ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * h a + ((t : ℝ) : EReal) * h b)
    (h_neg : ∀ ρ : ℝ, ρ < 0 → h ρ = ⊤)
    (h_proper : ∃ ρ : ℝ, h ρ ≠ ⊤) :
    LowerSemicontinuous (fun lam : ℝ => legendre h (-lam)) ∧
    Antitone (fun lam : ℝ => legendre h (-lam)) ∧
    (∀ a b t : ℝ, 0 ≤ t → t ≤ 1 →
      legendre h (-((1 - t) * a + t * b)) ≤
        ((1 - t : ℝ) : EReal) * legendre h (-a) + ((t : ℝ) : EReal) * legendre h (-b)) ∧
    (∀ lam : ℝ, lam < 0 → legendre h (-lam) = ⊤) ∧
    (∃ lam : ℝ, legendre h lam ≠ ⊤) := by sorry

end ShortWDRODual.Legendre
