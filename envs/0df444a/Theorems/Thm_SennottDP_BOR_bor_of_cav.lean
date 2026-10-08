-- Prove2me | Theorems.Thm_SennottDP_BOR_bor_of_cav
-- name    : SennottDP.BOR.bor_of_cav
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T11:30:15.520005+00:00
-- url     : https://prove2.me/theorems/85655de5-7cdd-4b5a-afe0-d698598e0d2c
-- title:
--   Corollary 7.5.9 — (CAV) implies (BOR)
-- statement:
--   Assume the (CAV) assumptions hold for the distinguished state $z$ and the policy $d$: $d$ is $z$ standard with positive recurrent class $R_d$; for every $U>0$ the set $D_U=\{i\mid C(i,a)\le U\text{ for some }a\}$ is finite; and for every $i\in S-R_d$ there is a policy $\theta_i\in\Re^*(z,i)$. Then the (BOR) assumptions hold, for $z$, $d$ and some $\varepsilon>0$.
--
--   These conditions are easy to verify when the costs of $\Delta$ are unbounded.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 148, Corollary 7.5.9

import Mathlib
import Definitions.Def_SennottDP_BOR_Assumptions

open scoped ENNReal NNReal
open Filter Topology

namespace SennottDP.BOR

/-- Sennott (1999), Corollary 7.5.9, p. 148. If the (CAV) assumptions hold for the distinguished
state `z` and the `z` standard policy `d`, then the (BOR) assumptions hold (for `z`, `d` and
some `ε > 0`). -/
theorem bor_of_cav {S Act : Type} [Countable S] (M : SennottDP.Discounted.MDC S Act) (z : S)
    (d : RandStationaryPolicy M) (hCAV : CAVAssumptions M z d) :
    ∃ ε : ℝ, BORAssumptions M z d ε := by sorry

end SennottDP.BOR
