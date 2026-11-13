-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_A_1
-- name    : PinwheelDensity.ExactRange.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:50.618955+00:00
-- url     : https://prove2.me/theorems/7f880a5b-9381-41d1-81eb-c0d45345f732
-- title:
--   Lemma A.1 — integer/rational and time-domain bridges
-- statement:
--   For an integer $a\ge1$ and a schedule $s:\mathbb N\to\mathbb N\cup\{\bot\}$, task $i$ is served with period $a$ if and only if every window of $a$ consecutive days contains an execution of $i$. Hence for a list $A$ of positive integers, schedulability with rational-period semantics coincides with classical pinwheel schedulability.
--
--   Moreover, for a nonempty list $A$ of positive integers, the following are equivalent:
--
--   1. $A$ is schedulable in one-sided time with idle days allowed;
--   2. $A$ has a periodic idle-free schedule;
--   3. $A$ has a schedule over $\mathbb Z$.
--
--   This lemma connects the three schedule models used in the paper, and it is what transfers the $\mathbb Z$-counting arguments of Section 2 to the guarantee over $\mathbb N$.
--
--   Differences from the source: none.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma A.1, p. 9 (PDF p. 9)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Lemma A.1, p. 9: for an integer `a ≥ 1`, service with period `a` is the window condition; on
lists of positive integers the rational notion is classical schedulability; and on nonempty such
lists it is equivalent to a periodic idle-free schedule and to a schedule over `ℤ`. -/
theorem lemma_A_1 :
    (∀ (s : ℕ → Option ℕ) (i a : ℕ), 1 ≤ a →
      (Serves s i (a : ℚ) ↔ ∀ t : ℕ, ∃ d : ℕ, t ≤ d ∧ d < t + a ∧ s d = some i)) ∧
    (∀ A : List ℕ, (∀ a ∈ A, 1 ≤ a) → (RatSchedulable (toQ A) ↔ Schedulable A)) ∧
    (∀ A : List ℕ, A ≠ [] → (∀ a ∈ A, 1 ≤ a) →
      (RatSchedulable (toQ A) ↔ HasPeriodicIdleFreeSchedule A) ∧
      (RatSchedulable (toQ A) ↔ ZSchedulable A)) := by sorry

end PinwheelDensity.ExactRange
