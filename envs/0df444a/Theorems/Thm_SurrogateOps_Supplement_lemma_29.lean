-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_lemma_29
-- name    : SurrogateOps.Supplement.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:42:21.949075+00:00
-- url     : https://prove2.me/theorems/f1afae17-8101-4ff0-8191-dc80690cb016
-- title:
--   Lemma 29, pp.18–19 — a $C^1$ map sends $B_\Delta(x_0)$ into the ball of radius $\bar M_{\nabla g}(x_0)\Delta$ about $g(x_0)$
-- statement:
--   Let $g=(g_1,\dots,g_m)^\top:\mathbb R^d\to\mathbb R^m$ be $C^1$ and $\bar\Delta>0$. For each $i$ let $M_{\nabla g_i}(x_0)\ge\max_{x\in B_{\bar\Delta}(x_0)}\|\nabla g_i(x)\|$, and let
--
--   $$
--   \bar M_{\nabla g}(x_0)=\bigl\|(M_{\nabla g_1}(x_0),\dots,M_{\nabla g_m}(x_0))^\top\bigr\|=\Bigl(\sum_{i=1}^m M_{\nabla g_i}(x_0)^2\Bigr)^{1/2}.
--   $$
--
--   Then for all $\Delta\in(0,\bar\Delta]$,
--
--   $$
--   g\bigl(B_\Delta(x_0)\bigr)\subseteq B_{\bar M_{\nabla g}(x_0)\Delta}\bigl(g(x_0)\bigr).
--   $$
--
--   The lemma controls how far the inner map of a composition moves the trust region, which is how the paper relates accuracy of the outer model near $f_1(x_0)$ to points $f_1(x)$, $x\in B_\Delta(x_0)$.
--
--   **Formalization Note** The component $g_i$ is `fun y => g y i`. The page writes the last entry of the vector as $M_{\nabla g_n}$; it is $M_{\nabla g_m}$.
--
--   Differences from the source:
--   - encoding: g : ℝ^d → ℝ^m with components g_i, the closed balls → g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m), components fun y => g y i, Metric.closedBall; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - reading: M̄_{∇g}(x₀) = ‖(M_{∇g₁}(x₀), …, M_{∇g_n}(x₀))^⊤‖ with the undefined index n → Real.sqrt (∑ i : Fin m, M i ^ 2), one entry per component of g; reason: n is not defined in the lemma and g has m components; the norm of ℝ^m is Euclidean
--   - generalization: M_{∇g_i}(x₀) = max_{x ∈ B_Δ̄(x₀)} ‖∇g_i(x)‖ → any M i with ‖∇g_i(x)‖ ≤ M i for all x ∈ B_Δ̄(x₀); reason: the maximum exists (continuous function on a compact ball) and is such a bound, so the Lean statement specializes to the source's
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Lemma 29, pp.18–19

import Mathlib

namespace SurrogateOps.Supplement

/-- **Lemma 29.** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through
Operations on Sub-models, arXiv:2112.08411v1, Lemma 29, pp.18–19.
Let `g = (g₁, …, g_m)ᵀ : ℝ^d → ℝ^m` be `C¹`, let `M_{∇g_i}(x0)` bound `‖∇g_i‖` on `B_Δ̄(x0)` and let
`M̄_{∇g}(x0) = ‖(M_{∇g₁}(x0), …, M_{∇g_m}(x0))ᵀ‖` (Euclidean norm). Then for all `Δ ∈ (0, Δ̄]`,
`g(B_Δ(x0)) ⊆ B_{M̄_{∇g}(x0)Δ}(g(x0))`.

**Formalization Note.** The page's last index `g_n` is a misprint for `g_m`; `Fin m` indexes the
components. The page defines `M_{∇g_i}(x0)` as the maximum of `‖∇g_i‖` on `B_Δ̄(x0)`; Lean takes any
upper bound `M i` (the maximum is one), and `M̄` is `√(∑ i, (M i)²)`. The component `g_i` is
`fun y => g y i`, its gradient `fderiv ℝ (fun y => g y i)` with the operator norm. -/
theorem lemma_29 {d m : ℕ} (g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin m))
    (x0 : EuclideanSpace ℝ (Fin d)) (Δbar : ℝ) (M : Fin m → ℝ)
    (hΔbar : 0 < Δbar) (hg : ContDiff ℝ 1 g)
    (hM : ∀ i, ∀ x ∈ Metric.closedBall x0 Δbar, ‖fderiv ℝ (fun y => g y i) x‖ ≤ M i) :
    ∀ Δ ∈ Set.Ioc 0 Δbar,
      g '' Metric.closedBall x0 Δ ⊆ Metric.closedBall (g x0) (Real.sqrt (∑ i, M i ^ 2) * Δ) := by sorry

end SurrogateOps.Supplement
