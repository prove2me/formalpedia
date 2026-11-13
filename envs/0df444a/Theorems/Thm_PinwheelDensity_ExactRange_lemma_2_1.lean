-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_1
-- name    : PinwheelDensity.ExactRange.lemma_2_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:50.823391+00:00
-- url     : https://prove2.me/theorems/c6e80f71-aa3c-4627-a0a3-7a462b6bfc2c
-- title:
--   Lemma 2.1 — adding a task to an instance with no free day
-- statement:
--   Let $P$ be a list of positive integers such that no schedule of $P$ over $\mathbb Z$ has a free day. Then for every positive integer $x$, the list $P+(x)$ has no schedule over $\mathbb Z$.
--
--   This turns every saturated core into a family of unschedulable instances with arbitrarily small additional density.
--
--   Differences from the source: none.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma 2.1, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Lemma 2.1, p. 4: if `P` admits no schedule over `ℤ` with a free day, then `P + (x)` has no
schedule over `ℤ`, for every positive integer `x`. -/
theorem lemma_2_1 (P : List ℕ) (hP : ∀ a ∈ P, 1 ≤ a) (hfree : NoScheduleWithFreeDay P)
    (x : ℕ) (hx : 1 ≤ x) : ¬ ZSchedulable (P ++ [x]) := by sorry

end PinwheelDensity.ExactRange
