-- Prove2me | Theorems.Thm_SchoolChoice_TTCQuota_ttcq_exists_cycle
-- name    : SchoolChoice.TTCQuota.ttcq_exists_cycle
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:00:22.10063+00:00
-- url     : https://prove2.me/theorems/e0408103-21f1-4f64-9d0d-5f56b710c4d4
-- title:
--   Section III.B — at every step of TTC with type-specific quotas there is at least one cycle
-- statement:
--   Consider the top trading cycles algorithm with type-specific quotas, run on capacities $q_s$ with no shortage of seats,
--   $$|I|\le \sum_{s\in S} q_s,$$
--   arbitrary type quotas $q_s^t$, student types $\tau$, school priorities and announced preferences $P$. Fix any step. Remove the students who have no remaining school with room for their type. If at least one student still remains, then some remaining student lies on a cycle of the pointing graph of that step: each remaining student points to her favourite school with room for her type, and each remaining school to its highest-priority remaining student.
--
--   This is the claim "There is at least one cycle" in the description of Steps 1 and $k$ on p. 22. It guarantees that every step with a remaining student removes at least one student, so the algorithm ends after at most $|I|$ steps.
--
--   **Formalization Note** As printed, the claim can fail when a remaining student cannot point (see the definition of the algorithm). It is stated for the step of the mission's convention, in which such stuck students have been removed first. The no-shortage hypothesis is the standing assumption of Section I; it is kept, although the statement does not need it.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), p. 22, Section III.B, Step 1 and Step k ("There is at least one cycle.")

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- Section III.B, Step 1 (p. 22): "There is at least one cycle." At every step of the top
trading cycles algorithm with type-specific quotas, once the stuck students (those with no
remaining school that has room for their type) have been removed, if some student still
remains then some remaining student is in a cycle. `run … t` is the state at the
beginning of Step `t + 1` and `prune τ (run … t)` the state after the stuck removal. -/
theorem ttcq_exists_cycle {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (t : ℕ)
    (hrem : (prune τ (run q qt τ pri P t)).rem.Nonempty) :
    ∃ i ∈ (prune τ (run q qt τ pri P t)).rem,
      InCycle P pri τ (prune τ (run q qt τ pri P t)) i := by sorry

end SchoolChoice.TTCQuota
