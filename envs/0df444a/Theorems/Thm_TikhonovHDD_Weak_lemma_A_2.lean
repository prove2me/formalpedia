-- Prove2me | Theorems.Thm_TikhonovHDD_Weak_lemma_A_2
-- name    : TikhonovHDD.Weak.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:14.202474+00:00
-- url     : https://prove2.me/theorems/2c47648a-b3b2-4b94-abfd-c695bcd0f798
-- title:
--   Lemma A.2 — a bounded-below locally absolutely continuous $F$ with $\dot F\le G\in L^1$ has a limit
-- statement:
--   Let $t_0>0$ and let $F:[t_0,+\infty)\to\mathbb R$ be locally absolutely continuous (absolutely continuous on every interval $[t_0,T]$) and bounded from below. Suppose there exists $G\in L^1([t_0,+\infty),\mathbb R)$ such that
--
--   $$\frac{d}{dt}F(t)\le G(t)\quad\text{for almost every } t\in[t_0,+\infty).$$
--
--   Then $\lim_{t\to+\infty}F(t)$ exists in $\mathbb R$.
--
--   This is the continuous counterpart of the convergence of quasi-Fejér monotone sequences; in the paper it gives the existence of $\lim_{t\to+\infty}\mathcal E_b(t)$ for the energy functional in the proof of Theorem 3.3.
--
--   **Formalization Note** $F$ is a function $\mathbb R\to\mathbb R$ whose values before $t_0$ are irrelevant; the derivative is Mathlib's `deriv F t`, which is the true derivative at almost every $t$ because an absolutely continuous function is differentiable almost everywhere. The standing $t_0>0$ of the paper is kept.
-- source:
--   Boţ, Csetnek, László, Tikhonov regularization of a second order dynamical system with Hessian driven damping, arXiv:1911.12845v2, p. 29, Lemma A.2 (stated from [1, Lemma 5.1])

import Mathlib

open Filter Topology Set MeasureTheory

namespace TikhonovHDD.Weak

theorem lemma_A_2 (t₀ : ℝ) (ht₀ : 0 < t₀) (F G : ℝ → ℝ)
    (hF : ∀ T : ℝ, t₀ ≤ T → AbsolutelyContinuousOnInterval F t₀ T)
    (hFbdd : BddBelow (F '' Ici t₀))
    (hG : IntegrableOn G (Ici t₀))
    (hFG : ∀ᵐ t ∂(volume.restrict (Ici t₀)), deriv F t ≤ G t) :
    ∃ L : ℝ, Tendsto F atTop (𝓝 L) := by sorry

end TikhonovHDD.Weak
