-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_fig1_solution_spaces
-- name    : VRPTWColGen92.Bound.fig1_solution_spaces
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T06:39:19.203074+00:00
-- url     : https://prove2.me/theorems/3ac55e12-4f67-468b-987b-0f5c2a2b4a44
-- title:
--   Sec. 3 and Figure 1, pp. 345–346 — the example has 11 feasible routes, 22 second-model paths and 12 2-cycle-free paths
-- statement:
--   In the four-node example of Figure 1 (capacity $Q = 6$, for every choice of the costs), the three solution spaces of Sec. 3 are exactly as follows.
--
--   1. The feasible routes are the eleven routes $(d,1,d)$, $(d,2,d)$, $(d,3,d)$, $(d,1,2,d)$, $(d,1,3,d)$, $(d,2,1,d)$, $(d,2,3,d)$, $(d,3,1,d)$, $(d,1,2,3,d)$, $(d,2,1,3,d)$, $(d,2,3,1,d)$.
--   2. The paths of the second model are those eleven routes and the eleven paths $(d,1,2,1,d)$, $(d,1,3,1,d)$, $(d,2,1,2,d)$, $(d,3,1,3,d)$, $(d,1,2,1,2,d)$, $(d,1,2,1,3,d)$, $(d,1,2,3,1,d)$, $(d,1,3,1,3,d)$, $(d,2,1,2,1,d)$, $(d,2,1,3,1,d)$, $(d,3,1,3,1,d)$: twenty-two in all.
--   3. The paths of the third model (no 2-cycle) are the eleven routes and $(d,1,2,3,1,d)$: twelve in all.
--
--   The example shows that the inclusions between the three solution spaces can be strict.
--
--   **Formalization Note.** The page's list for the second model prints $(d,2,1,2,d)$ twice; enumeration under the mission's conventions gives $(d,2,1,2,1,d)$ as the eleventh nonelementary path, and the statement lists that path. The counts need the capacity constraint "load $\le Q$" (with $<$, the path $(d,1,2,1,2,d)$ of load $6$ would drop out).
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), pp. 345–346, Sec. 3 and Figure 1

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_Fig1

namespace VRPTWColGen92.Bound
theorem fig1_solution_spaces (c : Fin 4 → Fin 4 → ℝ) :
    {p | IsRoute (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1]} :
        Set (List (Fin 4))) ∧
    {p | IsPath (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 2, 1], [1, 3, 1], [2, 1, 2], [3, 1, 3], [1, 2, 1, 2], [1, 2, 1, 3], [1, 2, 3, 1],
        [1, 3, 1, 3], [2, 1, 2, 1], [2, 1, 3, 1], [3, 1, 3, 1]} : Set (List (Fin 4))) ∧
    {p | IsPath3 (fig1 c) p} =
      ({[1], [2], [3], [1, 2], [1, 3], [2, 1], [2, 3], [3, 1], [1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 2, 3, 1]} : Set (List (Fin 4))) := by sorry
end VRPTWColGen92.Bound
