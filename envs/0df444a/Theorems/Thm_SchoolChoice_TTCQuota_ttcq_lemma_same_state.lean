-- Prove2me | Theorems.Thm_SchoolChoice_TTCQuota_ttcq_lemma_same_state
-- name    : SchoolChoice.TTCQuota.ttcq_lemma_same_state
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T08:04:11.775968+00:00
-- url     : https://prove2.me/theorems/bc89f001-eb98-4be9-83af-33be37bbc3e1
-- title:
--   Lemma (Appendix) for TTC with quotas — the state before the earlier removal step does not depend on i's report
-- statement:
--   Consider the top trading cycles algorithm with type-specific quotas, with capacities satisfying $|I|\le\sum_s q_s$, arbitrary type quotas, types and priorities. Fix a student $i$ and the announced preferences $P_j$ of all other students $j\ne i$. Compare two reports of $i$: $P_i$ and an arbitrary $Q_i$.
--
--   If at the beginning of some step student $i$ is still remaining under both reports, then at the beginning of that step the two runs have
--
--   1. the same set of remaining students,
--   2. the same school counters $c_s$ (hence the same remaining schools), and
--   3. the same type-specific counters $c_s^t$ (hence the same schools with room for each type).
--
--   This is the Lemma preceding the proof of Proposition 4. The paper states that the Lemma and its proof remain valid for the modified mechanism, and uses it in the proof of Proposition 7.
--
--   **Formalization Note** The paper assumes $i$ is removed at Step $T$ under one report and at Step $T^*\ge T$ under the other, and concludes about the beginning of Step $T$. Here the conclusion is stated at every step at whose beginning $i$ remains under both reports, which covers every step up to and including Step $T$; this is the form the proof establishes. The conclusion includes equality of the counters, which is what "the same schools" means for the modified mechanism, where pointing depends on the type-specific counters. Steps are indexed by the number $t$ of completed steps.
-- source:
--   Abdulkadiroğlu and Sönmez, School Choice: A Mechanism Design Approach, Columbia Univ. Economics Discussion Paper No. 0203-18 (July 2003), pp. 28–29, Lemma (Appendix); p. 30, proof of Proposition 7 ("The Lemma preceding the proof of Proposition 4 as well as its proof are valid for the modified mechanism.")

import Mathlib
import Definitions.Def_SchoolChoice_TTCQuota_Algorithm

namespace SchoolChoice.TTCQuota

/-- The Lemma of the Appendix (pp. 28–29), carried over to the modified mechanism (proof of
Proposition 7, p. 30). Fix the announced preferences of all students other than `i` (they
are `P j`, `j ≠ i`), and compare the report `P i` with any other report `Qi`. At every
step `t` at whose beginning (the beginning of Step `t + 1`) student `i` still remains
under both reports, the remaining students, the school counters and the type-specific
counters (hence the remaining schools and which of them have room for which type) are
the same under both reports. -/
theorem ttcq_lemma_same_state {I S Ty : Type} [Fintype I] [DecidableEq I] [Fintype S]
    [DecidableEq S] [Fintype Ty] [DecidableEq Ty]
    (q : S → ℕ) (qt : S → Ty → ℕ) (τ : I → Ty) (hq : Fintype.card I ≤ ∑ s, q s)
    (pri : S → Priority I) (P : I → Pref S) (i : I) (Qi : Pref S) (t : ℕ)
    (hi : i ∈ (run q qt τ pri P t).rem)
    (hi' : i ∈ (run q qt τ pri (Function.update P i Qi) t).rem) :
    (run q qt τ pri P t).rem = (run q qt τ pri (Function.update P i Qi) t).rem ∧
      (run q qt τ pri P t).cnt = (run q qt τ pri (Function.update P i Qi) t).cnt ∧
      (run q qt τ pri P t).tcnt = (run q qt τ pri (Function.update P i Qi) t).tcnt := by sorry

end SchoolChoice.TTCQuota
