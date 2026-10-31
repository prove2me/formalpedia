-- Prove2me | Theorems.Thm_SharedControl_ts_le_iff
-- name    : SharedControl.ts_le_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:07:52.241456+00:00
-- url     : https://prove2.me/theorems/3a89408f-423a-43ca-8c75-5740e872972c
-- title:
--   Proof of Proposition 1, p.4 — $t_s \le \pi_g + r_l$ iff $\bar r - r_l \le 2\pi_g$
-- statement:
--   Assume the standing assumptions, and let $t_s$ be the equilibrium transfer (the least nonnegative transfer satisfying Inequality (1)) and $\bar r = E[r]$. Then
--
--   $$
--   t_s \le \pi_g + r_l \iff \bar r - r_l \le 2\pi_g .
--   $$
--
--   The offer $t = \pi_g + r_l$ is the largest one the manager makes for every realization of $r$; the equivalence says it is acceptable to an uninformed stakeholder exactly when the mean uncertain part of the redistribution, $\bar r - r_l$, is at most the surplus $2\pi_g$ of a good project. It is the core of the proof of Proposition 1.
--
--   Differences from the source:
--   - reading: two halves of the proof: r̄ − rl ≤ 2πg gives ts ≤ πg + rl, and 2πg < r̄ − rl gives ts > πg + rl → one equivalence ts ≤ πg + rl ↔ r̄ − rl ≤ 2πg; reason: the second half is the contrapositive of the forward direction
--   - encoding: E[sg + t | mg ≥ t] in Inequality (1) → the integral of πg − r + t against the conditional measure P[|{mg ≥ t}], with Pr[mg ≥ t] > 0 required for t to satisfy (1); reason: a conditional expectation given a null event is undefined (Lean's cond returns the zero measure there); the least transfer satisfying (1) is unchanged
--   - generalization: r has a continuous distribution with support on [rl, rh], rl the minimum of the support → the law of r is atomless, r ∈ [rl, rh] almost surely, and every set {r < rl + ε}, {rh − ε < r} (ε > 0) has positive probability; reason: these three properties follow from supp(law r) = [rl, rh]; gaps inside (rl, rh) are also allowed, and no density is assumed, so the source's models are a special case
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, proof of Proposition 1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Standing
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts
import Definitions.Def_SharedControl_rbar

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, proof of Proposition 1, p.4 (PDF p.5): "Suppose the proposal
is good and that ¯r − rl ≤ 2πg. If the manager was to offer the stakeholder a transfer
t = πg + rl, the stakeholder’s expected payoff would be 2πg + rl − ¯r ≥ 0. It follows that the
equilibrium offer, ts, is less than or equal to πg + rl, and the stakeholder accepts this offer
for all realizations of r. Next, let 2πg < ¯r − rl. In this case, the stakeholder would reject
the offer t = πg + rl, and it must in the case that ts > πg + rl."

The equilibrium transfer satisfies `ts ≤ πg + rl` if and only if `r̄ − rl ≤ 2πg`.

**Formalization Note.** `ts` is `SharedControl.ts` (the least transfer satisfying (1)) and
`r̄` is `SharedControl.rbar`, the mean of `r`. The two halves of the quoted passage are the
two directions of the equivalence. -/
theorem ts_le_iff {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) (hM : Standing M) :
    ts M ≤ M.πg + M.rl ↔ rbar M - M.rl ≤ 2 * M.πg := by sorry

end SharedControl
