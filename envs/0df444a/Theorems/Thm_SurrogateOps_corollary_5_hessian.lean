-- Prove2me | Theorems.Thm_SurrogateOps_corollary_5_hessian
-- name    : SurrogateOps.corollary_5_hessian
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:51:26.429717+00:00
-- url     : https://prove2.me/theorems/503ddb52-421f-47e7-8fd3-ab7fe9efd8a6
-- title:
--   Corollary 5, p.4 — Hessian accuracy implies uniformly bounded model Hessians
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be $C^2$, $x_0\in\mathbb R^d$, $\bar\Delta>0$. If the class of models $\{\tilde f_\Delta\}_{(0,\bar\Delta]}$ provides order-$N$ Hessian accuracy of $f$ at $x_0$, then the class $\{\|\nabla^2\tilde f_\Delta\|\}_{(0,\bar\Delta]}$ is uniformly bounded at $x_0$. If it provides order-$N$ Hessian accuracy of $f$ near $x_0$, then $\{\|\nabla^2\tilde f_\Delta\|\}_{(0,\bar\Delta]}$ is uniformly bounded near $x_0$.
--
--   This is the Hessian analogue of the function and gradient statements of the corollary.
--
--   Differences from the source:
--   - encoding: the space ℝ^d, the closed ball B_Δ(x₀), a class of models {f̃_Δ}_{(0,Δ̄]} → EuclideanSpace ℝ (Fin d), Metric.closedBall x0 Δ, a map ℝ → E → ℝ used only on Set.Ioc 0 Δbar; reason: Lean convention; same instances
--   - encoding: the Hessian ∇²f as a matrix → fderiv ℝ (fderiv ℝ f) as a bilinear map; reason: the matrix and the second derivative determine each other; same instances
--   - reading: ‖·‖ on Hessians is unspecified → the operator norm of E →L[ℝ] E →L[ℝ] ℝ; reason: the spectral norm is the standard matrix norm in this literature and the one the proof's ‖ab^⊤‖ = ‖a‖‖b‖ uses; on a matrix it equals the operator norm of the bilinear map
--   - encoding: provides order-N accuracy: ∃ κ ≥ 0, in the hypothesis of an implication → κ universally quantified over the implication; reason: (∀ κ, P κ → Q) is equivalent to ((∃ κ, P κ) → Q)
--   - generalization: ∇f̃_Δ (resp. ∇²f̃_Δ) is assumed to exist → no regularity of the models is assumed; reason: the bound holds for fderiv as a total function, so the statement for differentiable models is a special case
-- source:
--   Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on Sub-models, arXiv:2112.08411v1, Corollary 5, p.4

import Mathlib
import Definitions.Def_SurrogateOps_HessAccAt
import Definitions.Def_SurrogateOps_HessAccNear
import Definitions.Def_SurrogateOps_UnifBddAt
import Definitions.Def_SurrogateOps_UnifBddNear

namespace SurrogateOps

/-- **Corollary 5, third sentence.** Chen, Hare, Jarry-Bolduc, Error Analysis of Surrogate Models Constructed through Operations on
Sub-models, arXiv:2112.08411v1, Corollary 5, p.4.
If `f ∈ C²` and `{f̃_Δ}` provides order-`N` Hessian accuracy of `f` at/near `x0`, then `{‖∇²f̃_Δ‖}`
is uniformly bounded at/near `x0`.

**Formalization Note.** `κ` is universally quantified, which is the same as an existential in the
hypothesis of each implication. -/
theorem corollary_5_hessian {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (fm : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (x0 : EuclideanSpace ℝ (Fin d)) (Δbar N κ : ℝ)
    (hΔbar : 0 < Δbar) (hf : ContDiff ℝ 2 f) :
    (HessAccAt f fm x0 Δbar N κ →
        UnifBddAt (fun Δ x => ‖fderiv ℝ (fderiv ℝ (fm Δ)) x‖) x0 Δbar) ∧
      (HessAccNear f fm x0 Δbar N κ →
        UnifBddNear (fun Δ x => ‖fderiv ℝ (fderiv ℝ (fm Δ)) x‖) x0 Δbar) := by sorry

end SurrogateOps
