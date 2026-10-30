-- Prove2me | Theorems.Thm_TwoAgentLateDP2004_LateLate_lemma_7_2
-- name    : TwoAgentLateDP2004.LateLate.lemma_7_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T14:49:16.176914+00:00
-- url     : https://prove2.me/theorems/d7433bbe-a331-41d0-b4cd-ecbd1fd71f9f
-- title:
--   Lemma 7.2 — finite table minima are attained; infinite entries have no partial schedule
-- statement:
--   Number all $n$ jobs in nondecreasing due-date order. Let $0\le i\le n$ and $h,k\ge0$. For the independent recurrence $C$:
--   $$C(i,h,k)=c\in\mathbb R\quad\Longrightarrow\quad \exists E\text{ admissible}:\ \sum_{j\in E}p_j=c,\qquad c\le\sum_{j\in F}p_j\ \text{for every admissible }F;$$
--   $$C(i,h,k)=+\infty\quad\Longrightarrow\quad \text{no admissible }E\text{ exists}.$$
--   Admissibility means a selected subset of the prefix that meets every selected due date in index order and omits at most $h$ A-jobs and $k$ B-jobs. Omission is permission to be late, not an assertion about actual lateness in a full sequence. The empty selected set has completion zero. Both finite attainment and the bound against every competitor are included.
--   The lemma identifies exactly what every table entry computes, without assuming its optimality in the hypotheses.
--
--   Differences from the source:
--   - generalization: two competing job sets with due dates and processing times → nonnegative real processing times, arbitrary real dates, and possibly empty owner classes; reason: no integrality restriction is imposed in §3; negative dates and empty classes extend the same formulas and include all source instances
--   - encoding: jobs and non-idling schedules on one machine → Fin n with an owner label and duplicate-free lists of all jobs; reason: each job belongs to exactly one agent; regular objectives permit removal of idle time without worsening either count
--   - reading: only C(0,0,0)=0 is printed → C(0,h,k)=0 for all nonnegative budgets; reason: the empty selected subset satisfies every at-most budget, forcing the unspecified zero row
--   - reading: minimum last-early completion over feasible partial schedules → minimum selected completion over admissible E, with omitted jobs consuming budgets; reason: for an A-job p=1,d=5 at i=1,h=1,k=0 the recurrence gives 0 but its actual early completion is 1; the preceding partial-schedule wording supports the selected-set reading
--   - encoding: finite times and positive infinity → WithTop real values; finite values quantified as real numbers; reason: no negative infinity, conditional infimum or default minimum is used; a zero budget is tested before decrementing
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici (2004), Scheduling Problems with Two Competing Agents, Operations Research 52(2):229–242, https://doi.org/10.1287/opre.1030.0092, Lemma 7.2, p.236 (PDF p.8); standing model §3 pp.231–232

import Mathlib
import Definitions.Def_TwoAgentLateDP2004_LateLate_Recurrence

namespace TwoAgentLateDP2004.LateLate

/-- Agnetis et al. (2004), Lemma 7.2, p.236 (PDF p.8), both clauses.
“Partial schedule” is read as a selected early subset; omitted jobs consume
budgets without asserting that they will actually be late in a full schedule. -/
theorem lemma_7_2 {n : ℕ} (I : Input n) (hEDD : Monotone I.d)
    (i h k : ℕ) (hi : i ≤ n) :
    (∀ c : ℝ, C I i h k = (c : WithTop ℝ) →
      (∃ E, Admissible I i h k E ∧ selectedCompletion I E = c) ∧
      ∀ E, Admissible I i h k E → c ≤ selectedCompletion I E) ∧
    (C I i h k = ⊤ → ¬ ∃ E, Admissible I i h k E) := by sorry

end TwoAgentLateDP2004.LateLate
