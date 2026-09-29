-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_lemma_same_state
-- name    : SchoolChoice.TTC.ttc_lemma_same_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:34:26.76506+00:00
-- url     : https://prove2.me/theorems/22bf6a34-01ed-4d11-ac4e-ddd3e58a8bad
-- title:
--   Lemma (Appendix) — before i's earlier removal step, the remaining students and schools do not depend on i's report
-- statement:
--   Let $I$, $S$ and capacities $(q_s)$ satisfy the no-shortage condition $|I|\le\sum_s q_s$, and fix strict priorities. Fix a student $i$, the announced preferences $P_j$ of every other student $j\ne i$, and two reports of student $i$: $P_i$ and an arbitrary $Q_i$. Write $P' = (Q_i, P_{-i})$.
--
--   For every $t\ge 0$: if student $i$ is still remaining at the beginning of Step $t+1$ both when she announces $P_i$ and when she announces $Q_i$, then at the beginning of Step $t+1$
--
--   1. the sets of remaining students coincide, and
--   2. the sets of remaining schools coincide,
--
--   under the two reports.
--
--   This is the Lemma the paper uses to prove Proposition 4: if $i$ is removed at Step $T$ under one report and at Step $T^*\ge T$ under the other, the remaining students and schools at the beginning of Step $T$ are the same.
--
--   **Formalization Note** "Suppose $i$ is removed at Step $T$ under $Q_i$ and at Step $T^*$ under $Q_i^*$, with $T\le T^*$" is rendered as "$i$ is still remaining at the beginning of the step under both reports", which avoids a removal-step function. The statement is thereby asserted at every step up to and including Step $T$, not only at Step $T$; this is exactly what the paper's proof establishes.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), pp. 28–29, Appendix, Lemma

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- The Lemma of the Appendix (pp. 28–29). Fix the announced preferences of all students
other than `i` (they are `P j`, `j ≠ i`), and compare the report `P i` with any other
report `Qi`. At every step `t` at whose beginning (the beginning of Step `t + 1`) student
`i` still remains under both reports, the remaining students and the remaining schools
are the same under both reports. -/
theorem ttc_lemma_same_state {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (t : ℕ)
    (hi : i ∈ (run q pri P t).rem)
    (hi' : i ∈ (run q pri (Function.update P i Qi) t).rem) :
    (run q pri P t).rem = (run q pri (Function.update P i Qi) t).rem ∧
      remSchools (run q pri P t) = remSchools (run q pri (Function.update P i Qi) t) := by sorry

end SchoolChoice.TTC
