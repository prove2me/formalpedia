-- Prove2me | Theorems.Thm_SennottDP_BOR_relValue_le_passageCost
-- name    : SennottDP.BOR.relValue_le_passageCost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:29:38.424817+00:00
-- url     : https://prove2.me/theorems/f1f342b8-ad88-4feb-ae42-451ac3eca203
-- title:
--   Lemma 7.4.1 — $h_\alpha(i)\le c_{iz}(\theta_i)$, hence (SEN2)
-- statement:
--   Let $z$ be a distinguished state and $\alpha\in(0,1)$ with $V_\alpha(z)<\infty$, and let $h_\alpha(i)=V_\alpha(i)-V_\alpha(z)$. If $i\ne z$ and $\theta_i\in\Re^*(i,z)$ (from $i$ the policy reaches $z$ with probability one, in finite expected time and at finite expected cost), then
--   $$
--   h_\alpha(i)\le c_{iz}(\theta_i).
--   $$
--   Hence, if $V_\alpha(z)<\infty$ for every $\alpha\in(0,1)$ and every $i\neq z$ has such a policy $\theta_i$, then (SEN2) holds for $z$ with $M(i)=c_{iz}(\theta_i)$ for $i\ne z$ and $M(z)=0$.
--
--   This is the basic way of verifying the upper bound (SEN2) through first passage costs.
--
--   **Formalization Note** $h_\alpha$ is valued in the extended reals; the inequality also asserts $V_\alpha(i)<\infty$. The value $M(z)=0$ is the book's remark on p. 133 ($h_\alpha(z)=0$).
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 140, Lemma 7.4.1

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Lemma 7.4.1, p. 140. Let `z` be a distinguished state and `α ∈ (0,1)` with
`V_α(z) < ∞`. If `i ≠ z` and `θ ∈ ℜ*(i,z)`, then `h_α(i) ≤ c_{iz}(θ)`. Hence, if `V_α(z) < ∞`
for every `α ∈ (0,1)` and every `i ≠ z` has a policy `θ_i ∈ ℜ*(i,z)`, then (SEN2) holds for `z`
with `M(i) = c_{iz}(θ_i)` for `i ≠ z` and `M(z) = 0`. -/
theorem relValue_le_passageCost {S Act : Type} [Countable S] [DecidableEq S] (M : SennottDP.Discounted.MDC S Act) (z : S) :
    (∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤ →
      ∀ i, i ≠ z → ∀ θ : SennottDP.Discounted.Policy M, InRStar θ i {z} →
        relValue M z α i ≤ ((passageCost θ i {z} : ℝ≥0∞) : EReal)) ∧
    ((∀ α : ℝ, 0 < α → α < 1 → valueFn M α z < ⊤) →
      ∀ θ : S → SennottDP.Discounted.Policy M, (∀ i, i ≠ z → InRStar (θ i) i {z}) →
        SEN2 M z (fun i => if i = z then 0 else (passageCost (θ i) i {z}).toReal)) := by sorry

end SennottDP.BOR
