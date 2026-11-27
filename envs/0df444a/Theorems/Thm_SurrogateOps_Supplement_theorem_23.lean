-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_23
-- name    : SurrogateOps.Supplement.theorem_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:40:55.526882+00:00
-- url     : https://prove2.me/theorems/9fbda938-ad49-56ff-892a-7068a66bf4b4
-- title:
--   Theorem 23, p.14 — gradient accuracy at $x_0$ of a quotient of two models exact at $x_0$, with constant $|1/f_2|\kappa^g_1\bar\Delta^{\cdot}+|f_1/f_2^2|\kappa^g_2\bar\Delta^{\cdot}$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^1$, $F=f_1/f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}/\tilde f_{2,\Delta}$, with $f_2(x)\neq0$ and $\tilde f_{2,\Delta}(x)\neq0$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$. Suppose that for $i=1,2$ the models are exact at $x_0$, $\tilde f_{i,\Delta}(x_0)=f_i(x_0)$ (order-$\infty$ function accuracy with constant $0$), and $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^g_i$ gradient accuracy of $f_i$ at $x_0$ with constant $\kappa^g_i(x_0)$. Let $N^g_F=\min\{N^g_1,N^g_2\}$. Then for every $\Delta\in(0,\bar\Delta]$
--
--   $$
--   \|\nabla F(x_0)-\nabla\tilde F_\Delta(x_0)\|\le K^g_F(x_0)\Delta^{N^g_F},\qquad
--   K^g_F(x_0)=\Bigl|\frac1{f_2(x_0)}\Bigr|\kappa^g_1(x_0)\bar\Delta^{N^g_1-N^g_F}+\Bigl|\frac{f_1(x_0)}{f_2^2(x_0)}\Bigr|\kappa^g_2(x_0)\bar\Delta^{N^g_2-N^g_F}.
--   $$
--
--   In particular $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^g_F$ gradient accuracy of $F$ at $x_0$.
--
--   Exactness at $x_0$ removes the function errors, so no smallness of $\bar\Delta$ is needed here.
--
--   **Formalization Note** The models are assumed differentiable at $x_0$.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - encoding: order-∞ function accuracy at a point with constant 0 → equality of model and function at that point for every Δ ∈ (0, Δ̄]; reason: the page states the equivalence itself (p.6)
--   - encoding: standing assumption of §4 (p.12): f₂(x) ≠ 0 and f̃_{2,Δ}(x) ≠ 0 for all Δ ∈ (0, Δ̄] and x ∈ B_Δ(x₀) → the hypothesis hne; reason: copied from the section's standing assumption; it is needed in Lean, where x / 0 = 0
--   - reading: ∇f̃_{i,Δ}(x₀) is used without stating the regularity of the models → DifferentiableAt ℝ (fm_i Δ) x0 for every Δ ∈ (0, Δ̄] at x₀; reason: the page's ∇f̃_{i,Δ}(x₀) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
--   - encoding: the constant K(x₀) → a variable fixed by an equation hypothesis (or written out in the conclusion); reason: same as the page's "Let" and "where"
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 23, p.14; standing assumptions of §4, p.12

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt

namespace SurrogateOps.Supplement

/-- **Theorem 23 (Gradient accuracy at `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate
Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 23, p.14 (standing
assumptions of §4, p.12).
For `F = f₁/f₂`, `F̃_Δ = f̃_{1,Δ}/f̃_{2,Δ}`, models exact at `x0` and `N^g_F = min{N^g_1, N^g_2}`:
`‖∇F(x0) - ∇F̃_Δ(x0)‖ ≤ K Δ^{N^g_F}` with
`K = |1/f₂(x0)| κ^g_1 Δ̄^{N^g_1 - N^g_F} + |f₁(x0)/f₂²(x0)| κ^g_2 Δ̄^{N^g_2 - N^g_F}`, and `{F̃_Δ}`
provides order-`N^g_F` gradient accuracy of `F` at `x0`.

**Formalization Note.** Order-∞ function accuracy at `x0` with constant `0` is the equality
`fm Δ x0 = f x0` (p.6). `hne` is the standing assumption of §4. `∇f̃_{i,Δ}(x0)` must exist; `hm₁`,
`hm₂` state that. -/
theorem theorem_23 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Ng₁ Ng₂ κg₁ κg₂ NF K : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hne : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, f₂ x ≠ 0 ∧ fm₂ Δ x ≠ 0)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₁ Δ) x0)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, DifferentiableAt ℝ (fm₂ Δ) x0)
    (he₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₁ Δ x0 = f₁ x0)
    (he₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, fm₂ Δ x0 = f₂ x0)
    (hg₁ : GradAccAt f₁ fm₁ x0 Δbar Ng₁ κg₁)
    (hg₂ : GradAccAt f₂ fm₂ x0 Δbar Ng₂ κg₂)
    (hNF : NF = min Ng₁ Ng₂)
    (hK : K = |1 / f₂ x0| * κg₁ * Δbar ^ (Ng₁ - NF) + |f₁ x0 / f₂ x0 ^ 2| * κg₂ * Δbar ^ (Ng₂ - NF)) :
    (∀ Δ ∈ Set.Ioc 0 Δbar,
      ‖fderiv ℝ (fun x => f₁ x / f₂ x) x0 - fderiv ℝ (fun x => fm₁ Δ x / fm₂ Δ x) x0‖
        ≤ K * Δ ^ NF) ∧
    ∃ κ, GradAccAt (fun x => f₁ x / f₂ x) (fun Δ x => fm₁ Δ x / fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
