-- Prove2me | Theorems.Thm_SchedSurvey_OPmtn_max_delta_pos
-- name    : SchedSurvey.OPmtn.max_delta_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:56:09.979636+00:00
-- url     : https://prove2.me/theorems/fee917a7-1d30-4f0c-b8c9-bd37826a29d7
-- title:
--   §5.2.2, p. 313 — for a decrementing set the maximum δ subject to (1), (2), (3) exists and is positive
-- statement:
--   Let $P=(p_{ij})$ be an $m\times n$ matrix of processing times $p_{ij}\ge 0$, rows indexed by the machines $M_i$ and columns by the jobs $J_j$ of an open shop with preemption allowed. Let $C$ be its largest row or column sum and $S$ a decrementing set of $P$. Consider the constraints on $\delta$:
--
--   1. if $p_{ij}\in S$ and row $i$ or column $j$ is tight, then $\delta\le p_{ij}$;
--   2. if $p_{ij}\in S$ and row $i$ (column $j$) is slack, then $\delta\le p_{ij}+C-\sum_k p_{ik}$ ($\delta\le p_{ij}+C-\sum_k p_{kj}$);
--   3. if row $i$ (column $j$) contains no element of $S$, then $\delta\le C-\sum_k p_{ik}$ ($\delta\le C-\sum_k p_{kj}$).
--
--   Then there is a largest $\delta$ satisfying (1)–(3), and it is strictly positive:
--
--   $$\exists\,\delta^\star>0:\ \delta^\star \text{ satisfies (1)–(3), and } \delta\le\delta^\star \text{ for every } \delta \text{ satisfying (1)–(3)}.$$
--
--   This is the step length of the algorithm of §5.2.2: each decrementing set yields a partial schedule of positive length.
--
--   **Formalization Note** Machines $M_1,\dots,M_m$ and jobs $J_1,\dots,J_n$ are indexed by `Fin m` and `Fin n`, which are 0-based: $M_i$ is index $i-1$ and $J_j$ is index $j-1$. No hypothesis $C>0$ is added: it follows from the existence of a decrementing set, because some line is tight and must contain a strictly positive entry.
-- source:
--   Graham, Lawler, Lenstra, Rinnooy Kan, Optimization and approximation in deterministic sequencing and scheduling: a survey, Ann. Discrete Math. 5 (1979), p. 313, §5.2.2, "… a partial schedule of length δ, for some δ > 0 … let δ be the maximum subject to (1), (2), (3)."

import Mathlib
import Definitions.Def_SchedSurvey_OPmtn_Model

namespace SchedSurvey.OPmtn

/-- §5.2.2, p. 313: for a decrementing set `S`, the maximum `δ` subject to (1), (2), (3) exists
and is strictly positive ("a partial schedule of length δ, for some δ > 0"). -/
theorem max_delta_pos {m n : ℕ} (P : Fin m → Fin n → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (C : ℝ) (hC : IsMaxLoad P C) (S : Finset (Fin m × Fin n))
    (hS : IsDecrementingSet P C S) :
    ∃ δ, 0 < δ ∧ IsMaxAdmissible P C S δ := by sorry

end SchedSurvey.OPmtn
