-- Prove2me | Theorems.Thm_SennottDP_DiscountedASM_value_le_liminf_VN
-- name    : SennottDP.DiscountedASM.value_le_liminf_VN
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-01T07:37:28.174415+00:00
-- url     : https://prove2.me/theorems/fc27cf90-843f-45cc-a062-5d743835b3ba
-- title:
--   Lemma 4.6.2 — $\liminf_N V^N_\alpha \ge V_\alpha$
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$, let $(\Delta_N)_{N\ge N_0}$ be an approximating sequence for $\Delta$, and fix a discount factor $\alpha\in(0,1)$. Let $V_\alpha$ be the discounted value function of $\Delta$ and $V^N_\alpha$ that of $\Delta_N$. Then for every $i\in S$,
--   $$
--   \liminf_{N\to\infty}V^N_\alpha(i)\ \ge\ V_\alpha(i).
--   $$
--
--   This is one half of the convergence $V^N_\alpha\to V_\alpha$: the approximating values can never undershoot the true value in the limit, whatever the approximating sequence. The other half is exactly Assumption DC($\alpha$).
--
--   **Formalization Note** $V^N_\alpha(i)$ is meaningful for $N\ge N_0$ with $i\in S_N$, which holds for all large $N$; the lim inf is taken in $[0,\infty]$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 75, Lemma 4.6.2

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC
import Definitions.Def_SennottDP_DiscountedASM_ApproxSeq

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

/-- Lemma 4.6.2 (p. 75): `liminf_{N→∞} V^N_α ≥ V_α`, pointwise on `S`. -/
theorem value_le_liminf_VN {S Act : Type} [Countable S] (M : MDC S Act)
    (Δs : ApproxSeq M) (α : ℝ≥0) (hα0 : 0 < α) (hα1 : α < 1) (i : S) :
    M.value α i ≤ liminf (fun N => Δs.VN α N i) atTop := by sorry

end SennottDP.DiscountedASM
