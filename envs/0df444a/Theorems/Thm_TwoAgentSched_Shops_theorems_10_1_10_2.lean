-- Prove2me | Theorems.Thm_TwoAgentSched_Shops_theorems_10_1_10_2
-- name    : TwoAgentSched.Shops.theorems_10_1_10_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:39:23.749299+00:00
-- url     : https://prove2.me/theorems/5d0e6b17-b863-4e0f-b3cf-7147abf62525
-- title:
--   Theorems 10.1 and 10.2 — $F2\|C^A_{\max}:C^B_{\max}$ and $O2\|C^A_{\max}:C^B_{\max}$ are NP-hard
-- statement:
--   **Theorems 10.1 and 10.2** of Agnetis, Mirchandani, Pacciarelli and Pacifici: the two-agent problems in which both agents minimize their own makespan, in the two-machine flow shop and in the two-machine open shop, are NP-hard, in the form proved in the paper:
--
--   $$\text{PARTITION}\ \le_p\ F2\,\|\,C^A_{\max}\le Q_A,\ C^B_{\max}\le Q_B\qquad\text{and}\qquad \text{PARTITION}\ \le_p\ O2\,\|\,C^A_{\max}\le Q_A,\ C^B_{\max}\le Q_B.$$
--
--   Here PARTITION asks whether a list of nonnegative integers splits into two parts of equal sum, the targets are the recognition problems "is there a feasible schedule in which every A-job completes by $Q_A$ and every B-job by $Q_B$?", every number is written in binary, and $\le_p$ is polynomial-time many-one reducibility (a polynomial-time computable map of codes that sends yes-instances to yes-instances and no-instances to no-instances).
--
--   Since the source problem is NP-complete in the ordinary sense, the two shop problems are NP-hard already when each agent only wants to finish its own jobs early, and the B-agent owns a single job.
--
--   **Formalization Note** NP-membership is not formalized. The target languages hold codes of instances with natural-number processing times and thresholds; start times are real. The paper's constructions have rational data ($\varepsilon=1/(k+1)$, $P/2$); a reduction scales them to integers. Theorem 10.1's printed equivalence holds only for even $P$ (and $P\ge2$ or $k\le1$), so a reduction treats the remaining cases separately.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 238, Theorem 10.1; p. 239, Theorem 10.2

import Mathlib
import Definitions.Def_TwoAgentSched_Shops_Model

namespace TwoAgentSched.Shops

open CookPvsNP ProjSchedTW.Complexity

/-- Theorems 10.1 and 10.2 (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, pp. 238–239):
`F2‖C^A_max : C^B_max` and `O2‖C^A_max : C^B_max` are NP-hard, in the form proved there: PARTITION
is polynomial-time many-one reducible to the recognition problem
`F2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B` and to `O2‖C^A_max ≤ Q_A, C^B_max ≤ Q_B`, all languages coded
in binary over `BSym`. -/
theorem theorems_10_1_10_2 :
    PolyReducible partitionLang flowLang ∧ PolyReducible partitionLang openLang := by sorry

end TwoAgentSched.Shops
