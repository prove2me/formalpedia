-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_6
-- name    : PinwheelDensity.ExactRange.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:54.677524+00:00
-- url     : https://prove2.me/theorems/98d0ab5c-bf23-4ae4-ad6c-266a893bcd85
-- title:
--   Lemma 2.6 — saturation of $Q_m$
-- statement:
--   Let $m\ge4$ and
--   $$Q_m=(m,\ m,\ (m+1)^{[m-3]},\ 2m+2,\ 3m+2).$$
--   Then no schedule of $Q_m$ over $\mathbb Z$ has a free day. Moreover $Q_m$ has a schedule over $\mathbb Z$, so it is saturated.
--
--   The cores $Q_m$ give the constant $7/6$ in the upper bound on $G(m)$.
--
--   Differences from the source: none.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma 2.6, p. 7 (PDF p. 7)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP

namespace PinwheelDensity.ExactRange

/-- Lemma 2.6 (Saturation of `Qₘ`), p. 7: no schedule of `Qₘ` over `ℤ` has a free day, `Qₘ` is
schedulable, and so it is saturated. -/
theorem lemma_2_6 (m : ℕ) (hm : 4 ≤ m) :
    NoScheduleWithFreeDay (coreQ m) ∧ ZSchedulable (coreQ m) ∧ Saturated (coreQ m) := by sorry

end PinwheelDensity.ExactRange
