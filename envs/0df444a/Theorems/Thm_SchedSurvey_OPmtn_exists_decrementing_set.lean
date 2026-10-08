-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_exists_decrementing_set
-- name    : SchedSurvey.OPmtn.exists_decrementing_set
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:55:15.469098+00:00
-- url     : https://prove2.me/theorems/0c81eddc-354d-4d2b-bb59-c15aa59fac86
-- title:
--   §5.2.2, p. 313 — every nonzero nonnegative matrix has a decrementing set
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $C=\max\{\max_j\sum_i p_{ij},\max_i\sum_j p_{ij}\}$, and call a row or column tight if its sum equals $C$ and slack otherwise. If $P\ne 0$, then $P$ has a **decrementing set**: a set $S$ of positions $(i,j)$ with
--
--   $$p_{ij}>0 \text{ for all }(i,j)\in S,\qquad |S\cap\text{line}| = 1 \text{ for every tight line},\qquad |S\cap\text{line}|\le 1 \text{ for every slack line},$$
--
--   where a line is a row or a column. The survey notes that such a set can be found by embedding $P$ in a doubly stochastic matrix and applying the Birkhoff–von Neumann theorem (via a linear assignment problem), referring to Lawler and Labetoulle (1978). It is what keeps the algorithm of §5.2.2 running until $P$ has been reduced to $0$.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. The hypothesis $P\ne 0$ is necessary: for $P=0$ with $m\ge 1$ every row is tight with sum $0$, and there is no positive entry to choose.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "By suitably embedding P in a doubly stochastic matrix …"

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: a decrementing set can be found (by the Birkhoff–von Neumann theorem,
[Lawler & Labetoulle 1978]). For a nonnegative, nonzero matrix `P` with maximal line sum `C`,
some set of strictly positive entries meets every tight row and tight column exactly once and
every slack row and slack column at most once. -/
theorem exists_decrementing_set {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hP0 : P ≠ 0) (C : ℝ) (hC : IsMaxLoad P C) :
    ∃ S : Finset (Fin m × Fin n), IsDecrementingSet P C S := by sorry

end SchedSurvey.OPmtn
