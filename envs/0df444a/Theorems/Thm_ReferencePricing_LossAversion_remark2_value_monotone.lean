-- Prove2me | Theorems.Thm_ReferencePricing_LossAversion_remark2_value_monotone
-- name    : ReferencePricing.LossAversion.remark2_value_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T08:34:01.796312+00:00
-- url     : https://prove2.me/theorems/c2ff7813-c1cb-44ee-8f3e-055d71568e3d
-- title:
--   Remark 2 — the value function $V(r)$ is increasing in the reference price
-- statement:
--   Consider the dynamic pricing problem with price set $P=[0,\bar p]$ ($\bar p>0$), reference price dynamics $r_{t+1}=\alpha r_t+(1-\alpha)p_t$ with $\alpha\in[0,1)$, discount factor $\beta\in(0,1)$, and demand $D(p,r)=d(p)+R(r-p,r)$ satisfying Assumption 1. Let $V$ be the value function of the sequence problem with per-period profit $\Pi(p,r)=pD(p,r)$. Then $V$ is increasing on $P$:
--   $$
--   r,r'\in P,\ r\le r'\ \Longrightarrow\ V(r)\le V(r').
--   $$
--
--   Higher reference prices are preferable for the firm. The proof of Theorem 1 uses this to rule out a steady state at the upper boundary $\bar p$.
--
--   **Formalization Note** "Increasing" is non-strict (`MonotoneOn` on $P$). Only Assumption 1 and the standing conditions on $\alpha$, $\beta$, $\bar p$ are assumed, as in the paper, where the remark precedes Assumptions 2–3.
-- source:
--   Popescu and Wu, Dynamic Pricing Strategies with Reference Effects, Operations Research 55(3), 2007, p. 417, Remark 2

import Mathlib
import Definitions.Def_RobustBooking_Shared_value
import Definitions.Def_RobustBooking_Shared_Assumptions
open RobustBooking.Shared

namespace ReferencePricing.LossAversion

/-- Remark 2 (Popescu and Wu 2007, p. 417): under Assumption 1 the value function `V` of the
sequence problem is increasing in the reference price on `P = [0, p̄]`. -/
theorem remark2_value_monotone (pbar α β : ℝ) (d : ℝ → ℝ) (R : ℝ → ℝ → ℝ)
    (hpbar : 0 < pbar) (hα₀ : 0 ≤ α) (hα₁ : α < 1) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (hA1 : Assumption1 pbar d R) :
    MonotoneOn (value (profit d R) α β pbar) (Set.Icc (0 : ℝ) pbar) := by sorry

end ReferencePricing.LossAversion
