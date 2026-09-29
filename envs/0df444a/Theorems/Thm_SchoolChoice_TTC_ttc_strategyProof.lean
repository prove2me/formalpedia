-- Prove2me | Theorems.Thm_SchoolChoice_TTC_ttc_strategyProof
-- name    : SchoolChoice.TTC.ttc_strategyProof
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T07:48:47.831483+00:00
-- url     : https://prove2.me/theorems/18773c36-79fd-4cfe-91d3-665156b0cb6a
-- title:
--   Proposition 4 — the top trading cycles mechanism is strategy-proof
-- statement:
--   Let $I$ be a finite set of students and $S$ a finite set of schools with capacities $(q_s)$ satisfying the no-shortage condition
--   $$|I|\le\sum_{s\in S} q_s .$$
--   Fix strict priorities $(\succ_s)_{s\in S}$, a profile $P=(P_j)_{j\in I}$ of announced strict preferences, a student $i$ whose true preference is $P_i$, and any alternative strict preference $Q_i$. Let $s$ be the school the top trading cycles mechanism assigns to $i$ at $P$ and $s'$ the school it assigns to $i$ at $(Q_i,P_{-i})$, where the other students' announcements are unchanged. Then both schools exist and
--   $$P_i(s)\le P_i(s'),$$
--   i.e. $i$ weakly prefers, under her true preference, the school she obtains by reporting truthfully.
--
--   Since $P_{-i}$, $Q_i$, the priorities and the capacities are arbitrary, no student can ever benefit by unilaterally misrepresenting her preferences: the top trading cycles mechanism is **strategy-proof** (Proposition 4). Truthful revelation is therefore a dominant strategy for every student.
--
--   **Formalization Note** Ranks are bijections onto `Fin`, rank $0$ being the favourite, so "weakly prefers $s$ to $s'$" is $P_i(s)\le P_i(s')$. The two existence clauses ensure the statement is not satisfied vacuously by an unassigned outcome.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 17, Proposition 4 (proof p. 29)

import Mathlib
import Definitions.Def_SchoolChoice_TTC_Algorithm

namespace SchoolChoice.TTC

/-- Proposition 4 (p. 17): the top trading cycles mechanism is strategy-proof. For all
capacities with no shortage of seats, all priorities, every profile of announced
preferences `P`, every student `i` whose true preference is `P i`, and every alternative
report `Qi`, student `i` is assigned a school `s` when reporting `P i` and a school `s'`
when reporting `Qi` (the others' reports unchanged), and she weakly prefers `s` to `s'`
under `P i` (rank `0` is the favourite). -/
theorem ttc_strategyProof {I S : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] (q : S → ℕ) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) :
    ∃ s s' : S, ttc q pri P i = some s ∧
      ttc q pri (Function.update P i Qi) i = some s' ∧ P i s ≤ P i s' := by sorry

end SchoolChoice.TTC
