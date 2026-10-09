-- Prove2me | Theorems.Thm_StochModelWC_ProxSubgrad_sec_3_2_vhat
-- name    : StochModelWC.ProxSubgrad.sec_3_2_vhat
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:43:16.419866+00:00
-- url     : https://prove2.me/theorems/37374b2b-a1d2-434a-9421-53ba761d3426
-- title:
--   §3.2, p. 15 — a subgradient v̂ ∈ ∂f(x̂) with ρ̄(x − x̂) ∈ ∂r(x̂) + v̂
-- statement:
--   Let $r : \mathbb R^d \to \mathbb R \cup \{+\infty\}$ be closed and convex with nonempty domain $D$, let $f : \mathbb R^d \to \mathbb R$ be $\rho$-weakly convex, and set $\varphi = f + r$. Fix $\bar\rho > \rho$ and a point $x$, and let $\hat x = \operatorname{prox}_{\varphi/\bar\rho}(x)$ be a minimizer of $y \mapsto \varphi(y) + \frac{\bar\rho}{2}\|y - x\|^2$. Then there is a vector $\hat v$ with
--   $$\hat v \in \partial f(\hat x) \qquad\text{and}\qquad \bar\rho(x - \hat x) \in \partial r(\hat x) + \hat v.$$
--
--   This is the optimality condition of the proximal subproblem split by the subdifferential sum rule; the vector $\hat v_t$ it produces at $x = x_t$ is the one used in Lemmas 3.2 and 3.3.
-- source:
--   Davis–Drusvyatskiy, Stochastic Model-Based Minimization of Weakly Convex Functions, arXiv:1803.06523v3, p. 15, §3.2, paragraph before Lemma 3.2

import Mathlib
import Definitions.Def_StochModelWC_ProxSubgrad_Basic

open MeasureTheory Filter Topology

namespace StochModelWC.ProxSubgrad

/-- §3.2, p. 15: if `x̂ = prox_{φ/ρ̄}(x)` for `φ = f + r`, then some `v̂ ∈ ∂f(x̂)` satisfies
`ρ̄(x − x̂) ∈ ∂r(x̂) + v̂`. -/
theorem sec_3_2_vhat {d : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (f r : EuclideanSpace ℝ (Fin d) → ℝ) (ρ ρbar : ℝ)
    (hD : D.Nonempty) (hr_cl : StochModelWC.ModelBased.IsClosedFn D r) (hr_cvx : ConvexOn ℝ D r)
    (hf : StochModelWC.ModelBased.IsWeaklyConvexOn Set.univ ρ f) (hρbar : ρ < ρbar)
    (x xhat : EuclideanSpace ℝ (Fin d))
    (hxhat : StochModelWC.ModelBased.IsProxPt D (fun y => f y + r y) (1 / ρbar) x xhat) :
    ∃ vhat ∈ frechetSubdiff Set.univ f xhat, ρbar • (x - xhat) - vhat ∈ frechetSubdiff D r xhat := by sorry

end StochModelWC.ProxSubgrad
