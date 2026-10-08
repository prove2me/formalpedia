-- Prove2me | Theorems.Thm_SennottDP_BOR_sen_of_monotone_value
-- name    : SennottDP.BOR.sen_of_monotone_value
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:01.882197+00:00
-- url     : https://prove2.me/theorems/92b593bf-82f3-45fe-9f6a-ec2832f03e2d
-- title:
--   Corollary 7.5.4 — increasing $V_\alpha$ plus a $0$ standard policy gives (SEN)
-- statement:
--   Let $S=\{0,1,2,\dots\}$ and assume that $V_\alpha(i)$ is increasing in $i$ for every $\alpha\in(0,1)$. If there exists a $0$ standard (randomized stationary) policy, then the (SEN) assumptions hold for the distinguished state $0$. Moreover every limit function $h$ is nonnegative and increasing in $i$:
--   $$
--   0\le h(i)\le h(i+1),\qquad i\ge0.
--   $$
--
--   This is the route to (SEN3) through a structural property of the discount value function.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 144, Corollary 7.5.4

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.4, p. 144. Let `S = {0, 1, 2, …}` and assume `V_α` is
increasing in `i` for every `α ∈ (0,1)`. If there exists a `0` standard (randomized stationary)
policy, then the (SEN) assumptions hold (for the distinguished state `0`), and every limit function
is nonnegative and increasing in `i`. -/
theorem sen_of_monotone_value {Act : Type} (M : SennottDP.Discounted.MDC ℕ Act)
    (hmono : ∀ α : ℝ, 0 < α → α < 1 → Monotone (valueFn M α))
    (hd : ∃ d : RandStationaryPolicy M, IsZStandard d.toPolicy 0) :
    SEN M 0 ∧ ∀ h : ℕ → ℝ, IsLimitFunction M 0 h → (∀ i, 0 ≤ h i) ∧ Monotone h := by sorry

end SennottDP.BOR
