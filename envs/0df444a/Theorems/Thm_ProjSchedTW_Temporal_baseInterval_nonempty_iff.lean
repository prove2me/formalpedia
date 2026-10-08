-- Prove2me | Theorems.Thm_ProjSchedTW_Temporal_baseInterval_nonempty_iff
-- name    : ProjSchedTW.Temporal.baseInterval_nonempty_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T14:43:17.853872+00:00
-- url     : https://prove2.me/theorems/73758b71-63ec-4a09-859a-21ef0e6da295
-- title:
--   Proposition 1.3.8 — the base time interval of a real activity is nonempty iff the activity is critical or near-critical
-- statement:
--   Let a project satisfy the standing assumption, let $L=LS_{n+1}\in\mathbb Z$, and suppose $N^+$ contains no cycle of positive length. With $ES_i=d_{0i}$, $LS_i=-d_{i0}$, $EC_i=ES_i+p_i$ and $TF_i=LS_i-ES_i$, for every real activity $i\in\{1,\dots,n\}$:
--   $$[LS_i,EC_i[\ \ne\ \emptyset\iff TF_i=0\ \text{ or }\ 0<TF_i<p_i,$$
--   that is, the base time interval of $i$ is nonempty exactly when $i$ is critical or near-critical.
--
--   A nonempty base time interval is a period during which activity $i$ is in progress in every time-feasible schedule respecting $L$; such intervals give lower bounds on resource usage in the resource-constrained chapters.
--
--   **Formalization Note.** The base time interval is a half-open interval of real time points.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 15, Proposition 1.3.8 (with Definition 1.3.7, p. 14)

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_TimeQuantities

namespace ProjSchedTW.Temporal

/-- Proposition 1.3.8 (p. 15): for a real activity `i`, the base time interval `[LS_i, EC_i[`
is nonempty if and only if `i` is critical or near-critical. -/
theorem baseInterval_nonempty_iff {n : ℕ} (P : Project n) (hP : P.StandingAssumption)
    (L : ℤ) (hL : ¬ HasPositiveCycle (P.N.plus L))
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hin : i ≠ Fin.last (n + 1)) :
    (P.baseInterval L i).Nonempty ↔ P.IsCritical L i ∨ P.IsNearCritical L i := by sorry

end ProjSchedTW.Temporal
