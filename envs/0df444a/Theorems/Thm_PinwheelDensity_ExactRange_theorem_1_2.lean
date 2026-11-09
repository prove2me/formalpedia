-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_2
-- name    : PinwheelDensity.ExactRange.theorem_1_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:55.731621+00:00
-- url     : https://prove2.me/theorems/76db44f8-e702-4a92-8c71-ffae45382c01
-- title:
--   Theorem 1.2 — minimum period four, sharp and attained
-- statement:
--   Every pinwheel instance with all periods at least $4$ and density at most $17/20$ is schedulable. Hence
--   $$G(4)=\frac{17}{20},$$
--   and the supremum is attained: $17/20$ is the greatest element of the threshold set $T(4)$.
--
--   This gives the case $a_1=4$ of the exact range.
--
--   Differences from the source:
--   - encoding: instances are written as nondecreasing lists → a `List ℕ` in any order; reason: tasks are list positions, and density and schedulability do not depend on the order (Lemma A.2), so the same instances are covered
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Theorem 1.2, p. 2 (PDF p. 2)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Theorem 1.2 (Minimum period four), p. 2, including attainment of the supremum. -/
theorem theorem_1_2 :
    Guarantee 4 (17 / 20) ∧ G 4 = 17 / 20 ∧ IsGreatest (ThresholdSet 4) (17 / 20) := by sorry

end PinwheelDensity.ExactRange
