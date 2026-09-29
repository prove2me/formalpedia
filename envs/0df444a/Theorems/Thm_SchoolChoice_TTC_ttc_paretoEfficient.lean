-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_paretoEfficient
-- name    : SchoolChoice.TTC.ttc_paretoEfficient
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:39:05.276581+00:00
-- url     : https://prove2.me/theorems/59618656-82d3-430d-9ea8-aa61269e924f
-- title:
--   Proposition 3 — the top trading cycles mechanism is Pareto efficient
-- statement:
--   Let $I$ be a finite set of students and $S$ a finite set of schools with capacities $(q_s)$ satisfying the no-shortage condition $|I|\le\sum_s q_s$. For all strict priorities $(\succ_s)$ and every announced strict preference profile $P$, the top trading cycles mechanism assigns every student a school, the resulting assignment $\mu$ is a matching, and $\mu$ is Pareto efficient with respect to $P$: there is no matching $\nu$ with
--   $$P_i(\nu(i))\le P_i(\mu(i)) \text{ for all } i \quad\text{and}\quad P_j(\nu(j))<P_j(\mu(j)) \text{ for some } j .$$
--
--   This is Proposition 3 of the paper; it distinguishes the top trading cycles mechanism from the Gale–Shapley student-optimal stable mechanism, which is not Pareto efficient.
--
--   **Formalization Note** Efficiency is with respect to the announced profile $P$ (the mechanism "always selects a Pareto efficient matching"), and the competitor $\nu$ ranges over capacity-respecting matchings.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 17, Proposition 3 (proof p. 28)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Model
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Proposition 3 (p. 17): the top trading cycles mechanism is Pareto efficient. For all
capacities with no shortage of seats, all priorities and every announced profile `P`, the
mechanism assigns every student a school, the assignment is a matching, and it is Pareto
efficient with respect to `P`. -/
theorem ttc_paretoEfficient {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) :
    ∃ μ : I → S, (∀ i, ttc q pri P i = some (μ i)) ∧ IsMatching q μ ∧
      IsParetoEfficient q P μ := by sorry

end SchoolChoice.TTC
