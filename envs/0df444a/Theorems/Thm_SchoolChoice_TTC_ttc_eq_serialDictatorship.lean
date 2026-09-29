-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_eq_serialDictatorship
-- name    : SchoolChoice.TTC.ttc_eq_serialDictatorship
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:44:01.369169+00:00
-- url     : https://prove2.me/theorems/bf6d04fb-fc35-4732-b8d4-fe1dc01832ef
-- title:
--   Section II.B — with a common priority ordering, TTC is serial dictatorship
-- statement:
--   Let $I$ be a finite set of students and $S$ a finite set of schools with capacities $(q_s)$ satisfying $|I|\le\sum_s q_s$. Suppose every school has the same priority ordering $\pi$ of the students. Then for every preference profile $P$, the top trading cycles mechanism coincides with the serial dictatorship induced by $\pi$:
--   $$\mathrm{TTC}(q,(\pi)_{s\in S},P) = \mathrm{SD}_\pi(q,P),$$
--   where in $\mathrm{SD}_\pi$ the student ranked first by $\pi$ is assigned her top choice, the next student her top choice among the remaining seats, and so on.
--
--   The paper uses this remark to present the top trading cycles mechanism as a generalization of serial dictatorship to school-specific priorities.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 16, Section II.B (serial dictatorship remark)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm
import Definitions.Def_SchoolChoice_TTC_SerialDictatorship

namespace SchoolChoice.TTC

/-- Section II.B (p. 16): when all schools have the same priority ordering `π`, the top
trading cycles mechanism reduces to the serial dictatorship induced by `π`. -/
theorem ttc_eq_serialDictatorship {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (π : Priority I) (pri : S → Priority I) (hpri : ∀ s, pri s = π) (P : I → Pref S) :
    ttc q pri P = serialDictatorship q π P := by sorry

end SchoolChoice.TTC
