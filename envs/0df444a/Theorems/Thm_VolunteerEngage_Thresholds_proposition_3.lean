-- Prove2me | Theorems.Thm_VolunteerEngage_Thresholds_proposition_3
-- name    : VolunteerEngage.Thresholds.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:40:38.751257+00:00
-- url     : https://prove2.me/theorems/d8e2daee-7096-43a7-b8fb-8c0ae473566f
-- title:
--   Proposition 3, p. 25 — on [τ_l, τ_{l−1}) every solution v of the Bellman equation (68)–(69) equals the explicit function u_l
-- statement:
--   Let the parameters $L,\theta_0,\eta_l,c_l,p,\kappa,\sigma$ satisfy the standing assumptions, with breakpoints $\theta_l$, cost $c$ (52), conjugate $\phi$ (66), shifted costs $\hat c_l$ ($\hat c_{L+1}=p$) and the functions $u_l$ of p. 24. Let $(\beta,v)$ solve the Bellman equation (68)–(69):
--   $$\beta=\tfrac12\sigma^2v'(x)+x\kappa\,(p-v(x))-\phi(p-v(x)),\quad x\ge0,\qquad v(0)=0,\ v\text{ increasing},\ \lim_{x\to\infty}v(x)=p,$$
--   with $v$ continuously differentiable on $[0,\infty)$. Define the thresholds (71) by $\tau_l=v^{-1}(p-\hat c_l)$, that is, $\tau_l\ge0$ and $v(\tau_l)=p-\hat c_l$, for $l=1,\dots,L$; and set $\tau_{L+1}=0$, $\tau_0=\infty$. Then for every $l=1,\dots,L+1$,
--   $$v(x)=u_l(x)\qquad\text{for all }x\in[\tau_l,\tau_{l-1}).$$
--
--   Between consecutive thresholds the optimal drift is constant, and on each such interval the value-function derivative $v$ is given in closed form by exponentials and the standard normal cdf. Evaluating $u_l$ at $\tau_{l-1}$ and inverting yields the thresholds $\tau_{L},\tau_{L-1},\dots,\tau_1$ recursively, which is how the paper computes its nested threshold policy.
--
--   **Formalization Note** The thresholds are passed as a sequence $\tau$ with the hypotheses $\tau_{L+1}=0$ and, for $l=1,\dots,L$, $\tau_l\ge0$ and $v(\tau_l)=p-\hat c_l$; since $v$ is strictly increasing on $[0,\infty)$ these determine $\tau_l=v^{-1}(p-\hat c_l)$, so the proposition's second clause "$\tau_l=v^{-1}(p-\hat c_l)$", which restates definition (71), is carried by this hypothesis and not posed separately. $\tau_0=\infty$ is encoded by dropping the upper bound when $l=1$. The statement is made for every solution $(\beta,v)$ of (68)–(69), whose definition includes $\beta>0$; existence of a solution is Theorem 1 of the paper (a separate mission). The standing assumptions are those of the Setting.
-- source:
--   Ata, Tongarlak, Lee, Field, A Dynamic Model for Managing Volunteer Engagement, arXiv:2312.02920v2, p. 25, Proposition 3 (with (71) on p. 22 and u_l on p. 24; τ_0 = ∞ from the proof, Online Supplement p. 10)

import Mathlib
import Definitions.Def_VolunteerEngage_Thresholds_Setting

namespace VolunteerEngage.Thresholds

/-- Proposition 3, p. 25: let `(β, v)` solve the Bellman equation (68)–(69) (with `v'` the
derivative of `v`), and let the thresholds be `τ_l = v⁻¹(p - ĉ_l)` for `l = 1, …, L` (71), i.e.
`τ_l ≥ 0` and `v(τ_l) = p - ĉ_l`, with `τ_{L+1} = 0` and `τ_0 = ∞`. Then for
`l = 1, …, L + 1` and every `x ∈ [τ_l, τ_{l-1})` we have `v(x) = u_l(x)`. -/
theorem proposition_3 (M : Model) (hM : M.Standing) (β : ℝ) (v v' : ℝ → ℝ)
    (hv : IsBellmanSol M β v v') (τ : ℕ → ℝ) (hτL : τ (M.L + 1) = 0)
    (hτ : ∀ l ∈ Finset.Icc 1 M.L, 0 ≤ τ l ∧ v (τ l) = M.p - chat M l) :
    ∀ l ∈ Finset.Icc 1 (M.L + 1), ∀ x : ℝ, τ l ≤ x → (l = 1 ∨ x < τ (l - 1)) →
      v x = u M β τ l x := by sorry

end VolunteerEngage.Thresholds
