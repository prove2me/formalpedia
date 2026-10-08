-- Prove2me | Theorems.Thm_VRPTWColGen92_Bound_window_reduction_preserves_paths
-- name    : VRPTWColGen92.Bound.window_reduction_preserves_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:38:59.001993+00:00
-- url     : https://prove2.me/theorems/71a2212b-fb64-495c-8964-20af6850ee6d
-- title:
--   Sec. 6.1, p. 349 — applying the time window reduction conditions at customers leaves the set of resource-feasible paths unchanged
-- statement:
--   Let $I$ be a VRPTW instance and let $(\rho_1, k_1), \dots, (\rho_m, k_m)$ be any finite sequence of pairs, each consisting of one of the four time window reduction conditions of Sec. 6.1 and a **customer** $k_\ell \ne d$. Let $I'$ be the instance obtained by applying the conditions in this order, each to the windows produced by the previous ones. Then a customer list is a path of the second model in $I$ if and only if it is one in $I'$:
--   $$\{\text{second-model paths of } I\} = \{\text{second-model paths of } I'\}.$$
--   Since routes and 2-cycle-free paths are second-model paths with a condition on the customer list only, the three solution spaces of Sec. 3 are all unchanged.
--
--   The paper applies the conditions to "reduce the time windows' width" of the same problem before solving it; this theorem is the statement that the reduction loses no path and admits no new one.
--
--   **Formalization Note.** The conditions are applied at customers only; the depot's start time is fixed at $T_d = 0$ and its window also constrains the return, so applying a condition at $d$ would mix the start and the return. The one-step case is the sequence of length one.
-- source:
--   Desrochers, Desrosiers & Solomon, A new optimization algorithm for the vehicle routing problem with time windows, Oper. Res. 40 (1992), p. 349, Sec. 6.1

import Mathlib
import Definitions.Def_VRPTWColGen92_Bound_Network
import Definitions.Def_VRPTWColGen92_Bound_WindowReduction

namespace VRPTWColGen92.Bound
theorem window_reduction_preserves_paths {n : ℕ} (I : Instance n)
    (steps : List (Rule × Fin (n + 1))) (hsteps : ∀ s ∈ steps, s.2 ≠ 0)
    (p : List (Fin (n + 1))) :
    IsPath I p ↔ IsPath (reduceSeq I steps) p := by sorry
end VRPTWColGen92.Bound
