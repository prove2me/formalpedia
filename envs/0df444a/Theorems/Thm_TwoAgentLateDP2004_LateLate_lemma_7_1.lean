-- Prove2me | Theorems.Thm_TwoAgentLateDP2004_LateLate_lemma_7_1
-- name    : TwoAgentLateDP2004.LateLate.lemma_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:48:34.740276+00:00
-- url     : https://prove2.me/theorems/801bbfa8-ab52-464e-80ca-77d079a5145a
-- title:
--   Lemma 7.1 — an optimal schedule has its actual early jobs first in EDD order
-- statement:
--   Let $I$ be a two-agent single-machine instance with real processing times $p_j\ge0$, real due dates $d_j$ and integer B-budget $Q$. Suppose that at least one feasible full schedule exists. Then
--   $$\exists s^*:\quad U_B(s^*)\le Q,\quad U_A(s^*)=\min_{s:\ U_B(s)\le Q}U_A(s),$$
--   and $s^*$ consists of precisely its actually early jobs in nondecreasing due-date order, followed by precisely its actually late jobs. Equality at the due date is early; due-date ties are allowed. There is no EDD-numbering hypothesis on the input in this lemma.
--   This is the structural statement on which the table-based optimization relies; optimality is for the original constrained problem over every permutation.
--
--   Differences from the source:
--   - generalization: two competing job sets with due dates and processing times → nonnegative real processing times, arbitrary real dates, and possibly empty owner classes; reason: no integrality restriction is imposed in §3; negative dates and empty classes extend the same formulas and include all source instances
--   - encoding: jobs and non-idling schedules on one machine → Fin n with an owner label and duplicate-free lists of all jobs; reason: each job belongs to exactly one agent; regular objectives permit removal of idle time without worsening either count
--   - encoding: there is an optimal schedule → a feasible instance admits such an optimal schedule; reason: the source presupposes feasibility; §3 explicitly allows infeasible instances
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, Lemma 7.1, p.236 (PDF p.8); standing model §3 pp.231–232

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_Model

namespace TwoAgentLateDP2004.LateLate

/-- Agnetis et al. (2004), Lemma 7.1, p.236 (PDF p.8).
Feasibility is the source's existence presupposition; there is no EDD input
assumption in this lemma. Empty owner sets and arbitrary real dates are allowed. -/
theorem lemma_7_1 {n : ℕ} (I : Input n) (Q : ℤ)
    (hf : ∃ s, Feasible I Q s) :
    ∃ s, Optimal I Q s ∧ EarlyFirstEDD I s := by sorry

end TwoAgentLateDP2004.LateLate
