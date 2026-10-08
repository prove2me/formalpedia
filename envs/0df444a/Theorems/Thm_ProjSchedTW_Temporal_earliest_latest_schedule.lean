-- Prove2me | Theorems.Thm_ProjSchedTW_Temporal_earliest_latest_schedule
-- name    : ProjSchedTW.Temporal.earliest_latest_schedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T14:42:48.145035+00:00
-- url     : https://prove2.me/theorems/afaec64c-7c28-4bc5-8817-32b784bff2d3
-- title:
--   §1.3, p. 12 — ES_i = d_0i is the earliest schedule and LS_i = −d_i0 the latest schedule
-- statement:
--   Let a project with AoN network $N$ satisfy the standing assumption (a path of nonnegative length from $0$ to each node and a path of length at least $p_i$ from each node $i$ to $n+1$). Let $L=LS_{n+1}\in\mathbb Z$ and suppose the temporal scheduling network $N^+$ contains no cycle of positive length. Let $d_{ij}$ be the longest path lengths in $N^+$, and put $ES_i=d_{0i}$, $LS_i=-d_{i0}$. Then:
--
--   1. $d_{0i}$ and $d_{i0}$ are finite for every $i\in V$;
--   2. $ES$ is the **earliest schedule**: $ES\in\mathcal S_T$ and $ES_i\le S_i$ for all $i\in V$ and all $S\in\mathcal S_T$;
--   3. $LS$ is the **latest schedule**: $LS\in\mathcal S_T$, $LS_{n+1}\le L$, and $S_i\le LS_i$ for all $i\in V$ and every $S\in\mathcal S_T$ with $S_{n+1}\le L$.
--
--   In particular $ES_{n+1}$ is the shortest project duration. The result turns temporal scheduling into two longest-path computations in $N^+$ (a forward and a backward pass).
--
--   **Formalization Note.** $\mathcal S_T$ is the set of time-feasible schedules of the project network $N$ (Definition 1.3.1). The book writes the latest-schedule property as "$LS_{n+1}\ge LS_i\ge S_i$ for all $S\in\mathcal S_T$"; since $LS_{n+1}$ is the maximum project duration, the comparison is over the schedules that respect it, $S_{n+1}\le L$, which is how it is stated here. The book's choice $L\in\{\bar d, ES_{n+1}\}$ with $\bar d\ge ES_{n+1}$ is covered: any integer $L$ for which $N^+$ has no cycle of positive length is allowed.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, §1.3, pp. 11–12 (earliest and latest schedule, Eq. (1.3.2), ES_i = d_0i and LS_i = −d_i0)

import Mathlib
import Definitions.Def_ProjSchedTW_Temporal_TimeQuantities

namespace ProjSchedTW.Temporal

/-- §1.3, p. 12: with `LS_{n+1} = L` and no cycle of positive length in `N⁺`, the longest path
lengths `d_0i` and `d_i0` in `N⁺` are finite, `ES = (d_0i)_i` is the earliest schedule (a
time-feasible schedule below every time-feasible schedule), and `LS = (-d_i0)_i` is the latest
schedule (a time-feasible schedule with `LS_{n+1} ≤ L` above every time-feasible schedule `S`
with `S_{n+1} ≤ L`). -/
theorem earliest_latest_schedule {n : ℕ} (P : Project n) (hP : P.StandingAssumption)
    (L : ℤ) (hL : ¬ HasPositiveCycle (P.N.plus L)) :
    (∀ i, dist (P.N.plus L) 0 i ≠ ⊥ ∧ dist (P.N.plus L) i 0 ≠ ⊥) ∧
    IsTimeFeasible P.N (fun i => (P.ES L i : ℝ)) ∧
    (∀ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S → ∀ i, (P.ES L i : ℝ) ≤ S i) ∧
    IsTimeFeasible P.N (fun i => (P.LS L i : ℝ)) ∧
    P.LS L (Fin.last (n + 1)) ≤ L ∧
    (∀ S : Fin (n + 2) → ℝ, IsTimeFeasible P.N S → S (Fin.last (n + 1)) ≤ L →
      ∀ i, S i ≤ (P.LS L i : ℝ)) := by sorry

end ProjSchedTW.Temporal
