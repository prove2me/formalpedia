-- Prove2me | Theorems.Thm_ResourceScheduling_Chain_threePartition_of_chainSchedule
-- name    : ResourceScheduling.Chain.threePartition_of_chainSchedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T11:27:45.522987+00:00
-- url     : https://prove2.me/theorems/293af8c3-6800-4982-b137-340dd057f132
-- title:
--   Proof of Theorem 7 ("only if") — a schedule with $C_{\max} \le 2tb$ gives a 3-PARTITION solution
-- statement:
--   Let $t, b, a_1,\dots,a_{3t}$ be a valid 3-PARTITION instance ($b>0$, $\sum_j a_j = tb$, $\tfrac14 b < a_j < \tfrac12 b$), and consider the instance of $P2\mid res111, chain, p_j=1\mid C_{\max}$ constructed from it in the proof of Theorem 7. If the constructed instance has a feasible schedule with
--   $$C_{\max} \le 2tb,$$
--   then $\{1,\dots,3t\}$ can be partitioned into $t$ disjoint 3-element sets $S_i$ with $\sum_{j\in S_i} a_j = b$.
--
--   This is the "only if" direction of the claim on which the proof of Theorem 7 rests. The bounds $\tfrac14 b < a_j < \tfrac12 b$ are used here, to conclude that each part has exactly three elements.
--
--   **Formalization Note.** The schedule may have arbitrary real start times; that both machines and the resource are saturated until time $2tb$ is a consequence to be proved, not an assumption.
-- source:
--   Błażewicz, Lenstra & Rinnooy Kan, Scheduling subject to resource constraints: classification and complexity, Discrete Appl. Math. 5 (1983), p. 19, proof of Theorem 7 ("only if" direction)

import Mathlib
import Definitions.Def_ResourceScheduling_Chain_Constructions

namespace ResourceScheduling.Chain
theorem threePartition_of_chainSchedule (P : ThreePartition) (hP : P.Valid)
    (h : P.chainInstance.HasScheduleWithin (2 * P.t * P.b)) :
    P.HasSolution := by sorry
end ResourceScheduling.Chain
