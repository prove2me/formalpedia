-- Prove2me | Theorems.Thm_ProjSchedTW_Complexity_maxCut_iff_stableSchedule
-- name    : ProjSchedTW.Complexity.maxCut_iff_stableSchedule
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T02:10:39.846158+00:00
-- url     : https://prove2.me/theorems/5cce91b6-247b-4515-b6a9-92870ba65c9b
-- title:
--   Proof of Proposition 3.4.2 — G has a cut of M edges iff the constructed instance has a 0/1 schedule of deviation ≥ M
-- statement:
--   Let $G$ be a simple graph on $V^G=\{1,\dots,\nu\}$ and $M\in\mathbb N$. Build the instance of $PS\infty|temp,\bar d|-\sum\sum w_{ij}|S_j-S_i|$ with $V=V^G\cup\{0,n+1\}$, $p_i=1$ for $i\in V^G$, minimum time lags $d^{\min}_{0i}=0$ and $d^{\min}_{i,n+1}=1$ for $i\in V^G$, $\bar d=2$, and $w_{ij}=1$ if $i$ and $j$ are adjacent in $G$, $w_{ij}=0$ otherwise. Then $G$ has a cut with at least $M$ edges if and only if there is a time-feasible schedule $S$ with $S_i\in\{0,1\}$ for all $i\in V^G$ and
--   $$\sum_{i\in V}\sum_{j\in V:\,j>i}w_{ij}\,|S_j-S_i|\ \ge\ M.$$
--
--   This is the correctness of the transformation from SIMPLE MAX CUT in the proof of Proposition 3.4.2; the book calls such a schedule stable.
--
--   **Formalization Note** Node $l$ of $G$ (`Fin ν`) is activity $l+1$. The deadline $S_{n+1}\le\bar d$ is part of time-feasibility. "A cut containing $M$ edges" is read as "at least $M$ edges", the SIMPLE MAX CUT question.
-- source:
--   Neumann, Schwindt & Zimmermann, Project Scheduling with Time Windows and Scarce Resources, 2nd ed., Springer 2003, p. 241, proof of Proposition 3.4.2 (transformation from SIMPLE MAX CUT)

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding
import Definitions.Def_ProjSchedTW_Complexity_TimeConstrained

namespace ProjSchedTW.Complexity

/-- Proof of Proposition 3.4.2 (p. 241): `G` has a cut with at least `M` edges iff the
constructed instance has a time-feasible schedule with `S_i ∈ {0, 1}` for all `i ∈ V^G` and
`∑_{i ∈ V} ∑_{j ∈ V, j > i} w_ij |S_j − S_i| ≥ M`. -/
theorem maxCut_iff_stableSchedule {ν : ℕ} (G : SimpleGraph (Fin ν)) (M : ℕ) :
    MaxCutYes G M ↔
      ∃ S, (maxCutProject G M).TimeFeasible S ∧
        (∀ i : Fin (ν + 2), i ≠ 0 → i ≠ Fin.last (ν + 1) → S i = 0 ∨ S i = 1) ∧
        (M : ℝ) ≤ (maxCutProject G M).deviation S := by sorry

end ProjSchedTW.Complexity
