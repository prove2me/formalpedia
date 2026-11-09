-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_theorem_1_3
-- name    : PinwheelDensity.ExactRange.theorem_1_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:52.932496+00:00
-- url     : https://prove2.me/theorems/3d01f46c-3d01-4dca-99d6-7bedce57c7ff
-- title:
--   Theorem 1.3 — minimum period five, sharp and attained
-- statement:
--   Every pinwheel instance with all periods at least $5$ and density at most $13/15$ is schedulable. Hence
--   $$G(5)=\frac{13}{15},$$
--   and the supremum is attained: $13/15$ is the greatest element of the threshold set $T(5)$.
--
--   This gives the case $a_1=5$ of the exact range and, by monotonicity of $G$, the lower bound on $G(6)$.
--
--   Differences from the source:
--   - encoding: instances are written as nondecreasing lists → a `List ℕ` in any order; reason: tasks are list positions, and density and schedulability do not depend on the order (Lemma A.2), so the same instances are covered
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Theorem 1.3, p. 2 (PDF p. 2)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Theorem 1.3 (Minimum period five), p. 2, including attainment of the supremum. -/
theorem theorem_1_3 :
    Guarantee 5 (13 / 15) ∧ G 5 = 13 / 15 ∧ IsGreatest (ThresholdSet 5) (13 / 15) := by sorry

end PinwheelDensity.ExactRange
