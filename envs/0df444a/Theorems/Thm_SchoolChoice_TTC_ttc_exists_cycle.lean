-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_exists_cycle
-- name    : SchoolChoice.TTC.ttc_exists_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:27:39.742428+00:00
-- url     : https://prove2.me/theorems/35fa5ea2-64c9-496c-bc4a-2da180b8b1b3
-- title:
--   Section II.B — at every step of the TTC algorithm with students remaining there is a cycle
-- statement:
--   Let $I$ be a finite set of students and $S$ a finite set of schools with capacities $(q_s)_{s\in S}$ such that there is no shortage of seats,
--   $$|I| \le \sum_{s\in S} q_s .$$
--   Fix strict priorities $(\succ_s)_{s\in S}$ and an announced preference profile $P$. For every $t\ge 0$, if some student remains at the beginning of Step $t+1$ of the top trading cycles algorithm, then some remaining student lies on a cycle of the pointing graph at that step.
--
--   This is the claim "there is at least one cycle" that the paper makes at Step 1 and at every Step $k$; it is what makes each step of the algorithm remove at least one student.
--
--   **Formalization Note** The claim is stated only for states reached by the algorithm from the initial state and under the no-shortage assumption: an arbitrary state can have remaining students and no remaining school, and then there is no cycle.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), pp. 15–16, Section II.B (Step 1 and Step k: there is at least one cycle)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Section II.B (p. 15): at every step of the top trading cycles algorithm at which some
student remains, there is at least one cycle, i.e. some remaining student is in a cycle.
`run q pri P t` is the state at the beginning of Step `t + 1`. -/
theorem ttc_exists_cycle {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (t : ℕ)
    (hrem : (run q pri P t).rem.Nonempty) :
    ∃ i ∈ (run q pri P t).rem, InCycle P pri (run q pri P t) i := by sorry

end SchoolChoice.TTC
