-- Prove2me | Theorems.Thm_UnrelatedSched_TwoApprox_lp_procedure_two_relaxed
-- name    : UnrelatedSched.TwoApprox.lp_procedure_two_relaxed
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T14:45:13.263437+00:00
-- url     : https://prove2.me/theorems/7fee0d56-0d04-4679-bfdf-f8d7cd2b9d89
-- title:
--   §3, pp. 5–6 — the LP rounding procedure is a 2-relaxed decision procedure
-- statement:
--   Let $P=(p_{ij})\in\mathbb N^{m\times n}$, let $V$ be a vertex selector for $P$ (for each $d\in\mathbb N$ it returns a vertex of (LP) with $d_1=\dots=d_m=t=d$, or 'none' exactly when that LP is infeasible), and let $D$ be the LP rounding procedure driven by $V$: it answers 'no' at $d$ exactly when $V$ returns 'none', and otherwise it answers with a schedule supported on the chosen vertex that solves (IP) with $d_1=\dots=d_m=t=d$. Then $D$ is a $2$-relaxed decision procedure: for every $d\in\mathbb N$,
--   1. if $D$ answers with a schedule $\sigma$, then $\operatorname{makespan}(\sigma)\le 2d$;
--   2. if $D$ answers 'no', then every schedule has makespan greater than $d$.
--
--   Together with Lemma 1 this gives the paper's 2-approximation algorithm.
--
--   **Formalization Note** The LP solver's choice of vertex is quantified over through the selector $V$; finding a vertex in polynomial time (the ellipsoid method) is not formalized.
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), pp. 5–6, §3

import Mathlib
import Definitions.Def_MatousekLP_Scheduling_Schedule
import Definitions.Def_UnrelatedSched_TwoApprox_DeadlineLP
import Definitions.Def_UnrelatedSched_TwoApprox_Algorithm

namespace UnrelatedSched.TwoApprox

/-- §3, pp. 5–6: the LP rounding procedure is a 2-relaxed decision procedure. -/
theorem lp_procedure_two_relaxed {m n : ℕ} (P : Matrix (Fin m) (Fin n) ℕ)
    (V : ℕ → Option (Matrix (Fin m) (Fin n) ℝ)) (hV : IsVertexSelector P V)
    (D : DecisionProcedure m n) (hD : IsLPRoundingProcedure P V D) :
    IsRelaxedDecisionProcedure P 2 D := by sorry

end UnrelatedSched.TwoApprox
