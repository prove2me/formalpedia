-- Prove2me | Theorems.Thm_SurrogateOps_Supplement_theorem_13
-- name    : SurrogateOps.Supplement.theorem_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:38:22.525785+00:00
-- url     : https://prove2.me/theorems/ab510870-6e45-514e-8a6e-02fe9f92a333
-- title:
--   Theorem 13, p.8 — a product of two models accurate near $x_0$ has Hessian accuracy of order $\min\{N^f_i,N^g_i,N^h_i\}$ near $x_0$
-- statement:
--   Let $f_1,f_2:\mathbb R^d\to\mathbb R$ be $C^2$, $F=f_1f_2$ and $\tilde F_\Delta=\tilde f_{1,\Delta}\tilde f_{2,\Delta}$. Suppose that for $i=1,2$ the class $\{\tilde f_{i,\Delta}\}_{(0,\bar\Delta]}$ provides order-$N^f_i$ function accuracy, order-$N^g_i$ gradient accuracy and order-$N^h_i$ Hessian accuracy of $f_i$ near $x_0$. Then $\{\tilde F_\Delta\}_{(0,\bar\Delta]}$ provides order-$N^{fgh}_F$ Hessian accuracy for $F$ near $x_0$, where
--
--   $$
--   N^{fgh}_F=\min\{N^f_1,N^f_2,N^g_1,N^g_2,N^h_1,N^h_2\}:
--   $$
--
--   some $\kappa\ge0$ independent of $\Delta$ and $x$ satisfies $\|\nabla^2F(x)-\nabla^2\tilde F_\Delta(x)\|\le\kappa\Delta^{N^{fgh}_F}$ for all $\Delta\in(0,\bar\Delta]$ and $x\in B_\Delta(x_0)$.
--
--   This is the Hessian counterpart of Theorem 10: near $x_0$ all three accuracy orders of the factors enter.
--
--   **Formalization Note** The models are assumed twice differentiable around every point of $B_\Delta(x_0)$ (`ContDiffAt ℝ 2`), which the page's $\nabla^2\tilde f_{i,\Delta}(x)$ presupposes.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0 → the constant κ is an explicit argument of the predicate, with 0 ≤ N and 0 ≤ κ as clauses; the order clause of the conclusion is ∃ κ; reason: a universally quantified κ in a hypothesis is the same as an existential one; the conclusion's κ depends on neither Δ nor x
--   - reading: ∇²f̃_{i,Δ}(x) is used without stating the regularity of the models → ContDiffAt ℝ 2 (fm_i Δ) x for every Δ ∈ (0, Δ̄] and every x ∈ B_Δ(x₀); reason: the page's ∇²f̃_{i,Δ}(x) presupposes it; Lean's fderiv is 0 at a non-differentiable point, where the product, quotient and chain rules fail
--   - encoding: min{…} of finitely many orders → nested binary min of the reals; reason: same value
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 13, p.8

import Mathlib
import Definitions.Def_SurrogateOps_FunAccNear
import Definitions.Def_SurrogateOps_GradAccNear
import Definitions.Def_SurrogateOps_HessAccNear

namespace SurrogateOps.Supplement

/-- **Theorem 13 (Hessian accuracy near `x0`).** Chen, Hare, Jarry-Bolduc, Error Analysis of
Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Theorem 13, p.8.
For `F = f₁f₂` and `F̃_Δ = f̃_{1,Δ}f̃_{2,Δ}`, if each class provides order-`N^f_i` function, order-`N^g_i`
gradient and order-`N^h_i` Hessian accuracy of `f_i` near `x0`, then `{F̃_Δ}` provides order-`N^{fgh}_F`
Hessian accuracy of `F` near `x0`, `N^{fgh}_F = min{N^f_1, N^f_2, N^g_1, N^g_2, N^h_1, N^h_2}`.

**Formalization Note.** `∇²f̃_{i,Δ}(x)` must exist on `B_Δ(x0)` for the page's statement to make
sense; `hm₁`, `hm₂` state that (`ContDiffAt`: every `C²` model qualifies). The conclusion's constant
is existential and depends on neither `Δ` nor `x`. -/
theorem theorem_13 {d : ℕ} (f₁ f₂ : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm₁ fm₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d))
    (Δbar Nf₁ Nf₂ Ng₁ Ng₂ Nh₁ Nh₂ κf₁ κf₂ κg₁ κg₂ κh₁ κh₂ NF : ℝ)
    (hΔbar : 0 < Δbar) (hf₁ : ContDiff ℝ 2 f₁) (hf₂ : ContDiff ℝ 2 f₂)
    (hm₁ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, ContDiffAt ℝ 2 (fm₁ Δ) x)
    (hm₂ : ∀ Δ ∈ Set.Ioc 0 Δbar, ∀ x ∈ Metric.closedBall x0 Δ, ContDiffAt ℝ 2 (fm₂ Δ) x)
    (hfa₁ : FunAccNear f₁ fm₁ x0 Δbar Nf₁ κf₁) (hfa₂ : FunAccNear f₂ fm₂ x0 Δbar Nf₂ κf₂)
    (hg₁ : GradAccNear f₁ fm₁ x0 Δbar Ng₁ κg₁) (hg₂ : GradAccNear f₂ fm₂ x0 Δbar Ng₂ κg₂)
    (hh₁ : HessAccNear f₁ fm₁ x0 Δbar Nh₁ κh₁) (hh₂ : HessAccNear f₂ fm₂ x0 Δbar Nh₂ κh₂)
    (hNF : NF = min (min (min Nf₁ Nf₂) (min Ng₁ Ng₂)) (min Nh₁ Nh₂)) :
    ∃ κ, HessAccNear (fun x => f₁ x * f₂ x) (fun Δ x => fm₁ Δ x * fm₂ Δ x) x0 Δbar NF κ := by sorry

end SurrogateOps.Supplement
