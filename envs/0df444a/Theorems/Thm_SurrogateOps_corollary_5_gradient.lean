-- Prove2me | Theorems.Thm_SurrogateOps_corollary_5_gradient
-- name    : SurrogateOps.corollary_5_gradient
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:09.28376+00:00
-- url     : https://prove2.me/theorems/483c6216-acbc-4b5a-bf02-d1fc2a6782ae
-- title:
--   Corollary 5, p.4 — gradient accuracy implies uniformly bounded model gradients
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be $C^1$, $x_0\in\mathbb R^d$, $\bar\Delta>0$. If the class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ provides order-$N$ gradient accuracy of $f$ at $x_0$, then the class $\{\|\nabla\tilde f_\Delta\|\}_{(0,\bar\Delta]}$ is uniformly bounded at $x_0$. If it provides order-$N$ gradient accuracy of $f$ near $x_0$, then $\{\|\nabla\tilde f_\Delta\|\}_{(0,\bar\Delta]}$ is uniformly bounded near $x_0$.
--
--   The bound obtained is the number $M_{\nabla\tilde f}(x_0)$ in the constants of Theorems 12 and 19.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the gradient ∇f and its Euclidean norm → fderiv ℝ f with the operator norm of E →L[ℝ] ℝ; reason: on EuclideanSpace the two norms agree by Riesz representation; same instances
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0, in the hypothesis of an implication → κ universally quantified over the implication; reason: (∀ κ, P κ → Q) is equivalent to ((∃ κ, P κ) → Q)
--   - generalization: ∇f̃_Δ (resp. ∇²f̃_Δ) is assumed to exist → no regularity of the models is assumed; reason: the bound holds for fderiv as a total function, so the statement for differentiable models is a special case
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Corollary 5, p.4

import Mathlib
import Definitions.Def_SurrogateOps_GradAccAt
import Definitions.Def_SurrogateOps_GradAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

namespace SurrogateOps

/-- **Corollary 5, second sentence.** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Corollary 5, p.4.
If `f ∈ C¹` and `{f̃_Δ}` provides order-`N` gradient accuracy of `f` at/near `x0`, then `{‖∇f̃_Δ‖}`
is uniformly bounded at/near `x0`.

**Formalization Note.** `κ` is universally quantified, which is the same as an existential in the
hypothesis of each implication. -/
theorem corollary_5_gradient {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : ContDiff ℝ 1 f) :
    (GradAccAt f fm x0 Δbar N κ →
        UnifBddAt (fun Δ x => ‖fderiv ℝ (fm Δ) x‖) x0 Δbar) ∧
      (GradAccNear f fm x0 Δbar N κ →
        UnifBddNear (fun Δ x => ‖fderiv ℝ (fm Δ) x‖) x0 Δbar) := by sorry

end SurrogateOps
