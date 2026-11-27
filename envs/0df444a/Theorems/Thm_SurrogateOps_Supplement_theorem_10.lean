-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_10
-- name    : SurrogateOps.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:37:55.073797+00:00
-- url     : https://prove2.me/theorems/13df7d10-0c5b-4ef3-9c2b-e0220300efe8
-- title:
--   Theorem 10, p.7 — a product of two models accurate near $x_0$ has gradient accuracy of order $\min\{N^f_i,N^g_i\}$ near $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^1$, $F=f_1f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\tilde f_{2,\Delta}$. Suppose that for $i=1,2$ the class $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy and order-$N^g_i$ gradient accuracy of $f_i$ near $x_0$, i.e. for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$
--
--   $$
--   |f_i(x)-\tilde f_{i,\Delta}(x)|\le\kappa^f_i\Delta^{N^f_i},\qquad \|\nabla f_i(x)-\nabla\tilde f_{i,\Delta}(x)\|\le\kappa^g_i\Delta^{N^g_i}.
--   $$
--
--   Then $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{fg}_F$ gradient accuracy of $F$ near $x_0$, where $N^{fg}_F=\min\{N^f_1,N^f_2,N^g_1,N^g_2\}$: there is a constant $\kappa\ge0$, independent of $\Delta$ and $x$, with $\|\nabla F(x)-\nabla\tilde F_\Delta(x)\|\le\kappa\Delta^{N^{fg}_F}$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$.
--
--   Away from $x_0$ the models cannot be assumed exact, so both the function and the gradient orders of the factors enter the order of the product.
--
--   **Formalization Note** The models are assumed differentiable at every point of $B_\Delta(x_0)$, which the page's $\nabla\tilde f_{i,\Delta}(x)$ presupposes.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - reading: ∇f̃_{i,Δ}(x) is used without stating the regularity of the models → DifferentiableAt ℝ (fm_i Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇f̃_{i,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 10, p.7

import Mathlib
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_GradAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 10 (Gradient accuracy near `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of
Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 10, p.7.
For `F = f₁f₂` and `F̃_Δ = f̃_{1,Δ}f̃_{2,Δ}`, if each class provides order-`N^f_i` function accuracy and
order-`N^g_i` gradient accuracy of `f_i` near `x0`, then `{F̃_Δ}` provides order-`N^{fg}_F` gradient
accuracy of `F` near `x0`, `N^{fg}_F = min{N^f_1, N^f_2, N^g_1, N^g_2}`.

**Formalization Note.** `∇f̃_{i,Δ}(x)` must exist on `B_Δ(x0)` for the page's statement to make
sense; `hm₁`, `hm₂` state that. The constants `κ` are arguments of the hypotheses; the conclusion's
constant is existential and depends on neither `Δ` nor `x`. -/
theorem theorem_10 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Nf₁ Nf₂ Ng₁ Ng₂ κf₁ κf₂ κg₁ κg₂ NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 1 f₁) (hf₂ : ContDiff ℝ 1 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, DifferentiableAt ℝ (fm₁ Δ) x)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, DifferentiableAt ℝ (fm₂ Δ) x)
    (hfa₁ : FunAccNear f₁ fm₁ x0 Δbar Nf₁ κf₁) (hfa₂ : FunAccNear f₂ fm₂ x0 Δbar Nf₂ κf₂)
    (hg₁ : GradAccNear f₁ fm₁ x0 Δbar Ng₁ κg₁) (hg₂ : GradAccNear f₂ fm₂ x0 Δbar Ng₂ κg₂)
    (hNF : NF = min (min Nf₁ Nf₂) (min Ng₁ Ng₂)) :
    ∃ κ, GradAccNear (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
