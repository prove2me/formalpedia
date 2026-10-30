-- Prove2me | Theorems.Thm_Timetabling_CT4_ct4Solve_spec
-- name    : Timetabling.CT4.ct4Solve_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:45:20.709928+00:00
-- url     : https://prove2.me/theorems/d82d640d-5eb6-40f6-a12d-1d6a6320b322
-- title:
--   Proposition 2.4: CT4 with at most 2 free periods per teacher in $O(n^2)$ time
-- statement:
--   **Proposition 2.4.** If in CT4 every teacher is available during at most 2 periods, there is an $O(n^2)$ algorithm for finding a timetable (or showing that none exists).
--
--   Precisely: there is an absolute constant $C$ such that for all $m, n, p$ and every well-formed CT4 instance $I$ with $m$ classes, $n$ teachers and $p$ periods in which every teacher is available ($\bar c_{jk} = 1$) in at most two periods, the run of $\mathsf{ct4Solve}(I)$ from tick $0$, with result $\mathrm{res}$ and final tick count $\mathrm{cost}$, satisfies
--
--   1. if $\mathrm{res}$ is a list $L$, then $L$ (read as $\bar x$) is a timetable: it satisfies (12)–(15);
--   2. $\mathrm{res}$ reports that no timetable exists if and only if no timetable exists;
--   3. $$\mathrm{cost} \le C\,(n^2 + 1),$$ uniformly in $m$ and $p$.
--
--   In general CT4 is NP-complete; this proposition isolates the case of at most two free periods per teacher, where a timetable is a stable set of $n$ nodes in a graph with a perfect matching, as a polynomial one.
--
--   Differences from the source:
--   - reading: every teacher is available during at most 2 periods → at most 2 periods k with c̄_jk = 1 (available and not preassigned); reason: availability enters CT4 only through c̄; raw availability ≤ 2 implies it, so the statement covers more instances
--   - reading: an instance of CT4 → the arrays r̄, b̄, c̄ together with the per-teacher lists of Table 1 (Instance, WellFormed); reason: with the arrays alone, finding a teacher's free period needs Ω(p) reads while n = 1, so O(n^2) is false; the lists are the same data rearranged
--   - encoding: classes, teachers, periods indexed from 1 → 0-based Fin m, Fin n, Fin p; bound C (n^2 + 1); reason: the + 1 only matters for n = 0, where the algorithm still takes O(1) ticks
--   - encoding: O(n^2) time → tick count of a StateM ℕ program reading input only through ticked accessors, C absolute; reason: unit-cost RAM model
--   - encoding: finding a timetable x̄ → a list of triples (i, j, k) read as x̄ through toTimetable; reason: a timetable has at most 2n nonzero entries; same timetables
--   - encoding: there is an O(n^2) algorithm (the limited backtracking of the proof) → witnessed by the specific algorithm ct4Solve, whose two trials per decision run interleaved; reason: the page does not order the steps of a decision and its reverse; all other rules are the paper's
-- source:
--   de Werra (1985), Proposition 2.4, p. 154; proof, pp. 154-155. D. de Werra, An introduction to timetabling, European Journal of Operational Research 19 (1985) 151-162, doi:10.1016/0377-2217(85)90167-5

import Mathlib
import Definitions.Def_Timetabling_CT4_Instance_WellFormed
import Definitions.Def_Timetabling_CT4_Feasible
import Definitions.Def_Timetabling_CT4_toTimetable
import Definitions.Def_Timetabling_CT4_ct4Solve

namespace Timetabling.CT4

/-- **Proposition 2.4.**
de Werra, *An introduction to timetabling*, EJOR 19 (1985), Proposition 2.4, p. 154: "If in CT4
every teacher is available during at most 2 periods, there is an O(n^2) algorithm for finding a
timetable (or showing that none exists)."

There is an absolute constant `C` such that for all `m`, `n`, `p` and every well-formed CT4
instance `I` with `m` classes, `n` teachers and `p` periods in which every teacher is free
(`c̄_jk = 1`) in at most 2 periods, the run of `ct4Solve I` from tick `0`, with result `res` and
final tick count `cost`, satisfies

1. if `res = some L`, then `L` (read through `toTimetable`) is a timetable: it satisfies
   (12)–(15);
2. `res = none` if and only if no timetable exists;
3. `cost ≤ C (n^2 + 1)`.

**Formalization Note.** Running time is the tick count of the unit-cost model of
`Timetabling.Cost.tick`; the input includes the per-teacher lists of Table 1; the bound does not
depend on `m` or `p`; the `+ 1` only matters for `n = 0`. -/
theorem ct4Solve_spec :
    ∃ C : ℕ, ∀ {m n p : ℕ} (I : Instance m n p), I.WellFormed →
      (∀ j, (Finset.univ.filter fun k => I.cbar j k = 1).card ≤ 2) →
      (∀ L, ((ct4Solve I).run 0).1 = some L → Feasible I (toTimetable L)) ∧
        (((ct4Solve I).run 0).1 = none ↔ ¬ ∃ x, Feasible I x) ∧
        ((ct4Solve I).run 0).2 ≤ C * (n ^ 2 + 1) := by sorry

end Timetabling.CT4
