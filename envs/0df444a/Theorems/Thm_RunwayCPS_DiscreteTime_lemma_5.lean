-- Prove2me | Theorems.Thm_RunwayCPS_DiscreteTime_lemma_5
-- name    : RunwayCPS.DiscreteTime.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:16:45.455099+00:00
-- url     : https://prove2.me/theorems/11c42bb1-2bd0-48a4-aead-0646359415c9
-- title:
--   Lemma 5 — every source-sink path of the modified network represents a feasible schedule
-- statement:
--   Assume $k\ge 1$ and that the separations satisfy the polygon inequalities of three or more hops. Let $(i_1,t_1,d_1),\dots,(i_n,t_n,d_n)$ be a source-sink path of the discrete-time triangle-inequality modified network. Then the schedule that lands $\mathrm{fin}(i_p)$ in position $p$ at time $t_p$ is feasible: it is a $k$-CPS sequence, respects the precedence constraints and the time windows, and
--   $$
--   t_q-t_p\;\ge\;\delta_{\mathrm{fin}(i_p)\,\mathrm{fin}(i_q)}\qquad\text{for all } p<q .
--   $$
--
--   This is one half of the correctness of the §6.2 algorithm: minimizing over paths never returns an infeasible schedule.
--
--   **Formalization Note** The polygon-inequality hypothesis is added. The paper's proof checks only pairs one and two positions apart; without the quadrilateral inequality the lemma is false (a minimum-cost path can be infeasible). Section 7 asserts these inequalities for mixed arrivals and departures. The triangle inequality is not assumed.
-- source:
--   Balakrishnan & Chandran, Algorithms for Scheduling Runway Operations Under Constrained Position Shifting, Oper. Res. 58(6) (2010), pp. 1658–1659, Lemma 5

import Mathlib
import Definitions.Def_RunwayCPS_DiscreteTime_ModifiedNetwork

namespace RunwayCPS.DiscreteTime

/-- Lemma 5 (p. 1658): every source-sink path of the discrete-time triangle-inequality modified
network represents a feasible schedule. Stated for `k ≥ 1` (§6.2, so that every node of stage
`p ≥ 2` has a penultimate aircraft) and under the polygon inequalities of three or more hops, which
the separations must satisfy for the lemma to hold. -/
theorem lemma_5 {n : ℕ} [NeZero n] (I : Instance n) (hk : 1 ≤ I.k)
    (hpoly : PolygonIneq I.δ) (P : ℕ → MNode n) (hP : IsMPath I P) :
    IsFeasible I (mSeq P) (mTimes P) := by sorry

end RunwayCPS.DiscreteTime
