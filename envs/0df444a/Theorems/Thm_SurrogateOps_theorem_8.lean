-- Prove2me | Theorems.Thm_SurrogateOps_theorem_8
-- name    : SurrogateOps.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:50:49.050766+00:00
-- url     : https://prove2.me/theorems/7f6d656d-6fa4-4a27-b0a8-2b70ce8c12ad
-- title:
--   Theorem 8, p.6 — gradient accuracy of a product of two models exact at $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^1$, with $F=f_1f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\tilde f_{2,\Delta}$. Suppose that for $i=1,2$ and all $\Delta\in(0,\bar\Delta]$ the model satisfies $\tilde f_{i,\Delta}(x_0)=f_i(x_0)$ (order-$\infty$ function accuracy at $x_0$ with constant $0$), and that $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy of $f_i$ at $x_0$ with constant $\kappa^g_i(x_0)$. Let $N^g_F=\min\{N^g_1,N^g_2\}$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla F(x_0)-\nabla\tilde F_\Delta(x_0)\|\le K^g_F(x_0)\Delta^{N^g_F},
--   $$
--
--   where
--
--   $$
--   K^g_F(x_0)=|f_2(x_0)|\kappa^g_1(x_0)\bar\Delta^{N^g_1-N^g_F}+|f_1(x_0)|\kappa^g_2(x_0)\bar\Delta^{N^g_2-N^g_F}.
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^g_F$ gradient accuracy of $F$ at $x_0$.
--
--   Making the models exact at $x_0$ removes the model bounds from the constant.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; reason: the theorems name the constant κ_i(x₀); the order clause of the conclusion is ∃ κ
--   - encoding: order-∞ function accuracy at x₀ with constant κ^f_i(x₀) = 0 → fm i Δ x0 = f i x0 for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - reading: ∇f̃_{i,Δ}(x₀) is used without stating that the models are differentiable → DifferentiableAt ℝ (fm i Δ) x0 for every Δ ∈ (0, Δ̄]; reason: the page's ∇f̃_{i,Δ}(x₀) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product rule fails
--   - encoding: N^g_F and K^g_F(x₀) → the number is a variable fixed by an equation or IsLeast hypothesis; reason: same as the page's "Let" and "where"
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 8, p.6

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt

namespace SurrogateOps

/-- **Theorem 8 (Gradient accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Theorem 8, p.6.
For `F = f₁f₂`, `F̃_Δ = f̃_{1,Δ}f̃_{2,Δ}`, models exact at `x0` and `N_F = min{N₁, N₂}`:
`‖∇F(x0) - ∇F̃_Δ(x0)‖ ≤ K Δ^{N_F}` with `K` the constant of the page, and `{F̃_Δ}` provides order-`N_F`
gradient accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy at `x0` with constant `0` is the equality
`fm Δ x0 = f x0` (p.6). `∇f̃_Δ(x0)` must exist for the page's statement to make sense; `hm₁`, `hm₂`
state that. -/
theorem theorem_8 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar N₁ N₂ κ₁ κ₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₂ Δ) x0)
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ x0 = f₂ x0)
    (hg₁ : GradAccAt f₁ fm₁ x0 Δbar N₁ κ₁)
    (hg₂ : GradAccAt f₂ fm₂ x0 Δbar N₂ κ₂)
    (hNF : NF = min N₁ N₂)
    (hK : K = |f₂ x0| * κ₁ * Δbar ^ (N₁ - NF) + |f₁ x0| * κ₂ * Δbar ^ (N₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => f₁ x * f₂ x) x0 - fderiv ℝ (fun x => fm₁ Δ x * fm₂ Δ x) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, GradAccAt (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps
