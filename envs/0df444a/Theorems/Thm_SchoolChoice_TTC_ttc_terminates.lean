-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_terminates
-- name    : SchoolChoice.TTC.ttc_terminates
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:33:14.010638+00:00
-- url     : https://prove2.me/theorems/8bffea4a-c0c4-4bc6-9279-5b5aba112fdb
-- title:
--   Section II.B — the TTC algorithm ends within |I| steps with a matching
-- statement:
--   Let $I$ be a finite set of students and $S$ a finite set of schools with capacities $(q_s)_{s\in S}$ satisfying the no-shortage condition
--   $$|I| \le \sum_{s\in S} q_s .$$
--   For all strict priorities and every announced preference profile $P$, after $|I|$ steps of the top trading cycles algorithm no student remains, and the resulting assignment is a matching: there is $\mu : I\to S$ such that every student $i$ is assigned the school $\mu(i)$ by the mechanism and
--   $$\#\{i : \mu(i)=s\}\le q_s \qquad\text{for every school } s.$$
--
--   This makes precise the paper's remarks that the algorithm terminates when all students are assigned a seat and that there can be no more steps than students; it shows that the top trading cycles mechanism is a well-defined student assignment mechanism.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 16, Section II.B (termination remark)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Section II.B (p. 16): the algorithm terminates within `card I` steps — after
`card I` steps no student remains — and the resulting assignment is a matching:
every student is assigned some school and no school receives more students than its
capacity. -/
theorem ttc_terminates {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    (run q pri P (Fintype.card I)).rem = ∅ ∧
      ∃ μ : I → S, (∀ i, ttc q pri P i = some (μ i)) ∧ IsMatching q μ := by sorry

end SchoolChoice.TTC
