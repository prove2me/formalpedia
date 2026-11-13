-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_prop_2_3
-- name    : PinwheelDensity.ExactRange.prop_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:36.347447+00:00
-- url     : https://prove2.me/theorems/4d3bec0b-9e91-4195-91cd-2f23022b6b80
-- title:
--   Proposition 2.3 — sharpness at every minimum period
-- statement:
--   For every $m\ge1$ and $x\ge1$, the instance $(m,(m+1)^{[m-1]},x)$ is unschedulable and has density
--   $$c(m)+\frac1x.$$
--   In particular $G(m)\le c(m)$.
--
--   This is why $c(m)$ is the bound conjectured for smallest period $m$, and it gives the upper half of Theorems 1.2 and 1.3.
--
--   Differences from the source:
--   - encoding: the instance is schedulable, with a schedule over ℤ in Section 2 and in Kawamura's wording → `Schedulable`, the one-sided schedule over ℕ with idle days; reason: the two notions are equivalent on nonempty lists of positive integers (Lemma A.1)
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Proposition 2.3, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP

namespace PinwheelDensity.ExactRange

/-- Proposition 2.3 (Sharpness), p. 4. -/
theorem prop_2_3 (m : ℕ) (hm : 1 ≤ m) :
    (∀ x : ℕ, 1 ≤ x → ¬ Schedulable (sharpCore m ++ [x]) ∧
      density (sharpCore m ++ [x]) = c m + 1 / (x : ℚ)) ∧
    G m ≤ ((c m : ℚ) : ℝ) := by sorry

end PinwheelDensity.ExactRange
