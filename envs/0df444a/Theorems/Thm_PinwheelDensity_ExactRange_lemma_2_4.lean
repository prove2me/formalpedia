-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_4
-- name    : PinwheelDensity.ExactRange.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:43.190601+00:00
-- url     : https://prove2.me/theorems/f67cdb14-f8a3-48fb-8c75-75c3974303f8
-- title:
--   Lemma 2.4 — saturation of $P_n$
-- statement:
--   Let $n\ge3$ and
--   $$P_n=(n-1,\ n^{[n-3]},\ 2n-1,\ 4n-1,\ 5n).$$
--   Then no schedule of $P_n$ over $\mathbb Z$ has a free day. Moreover $P_n$ has a schedule over $\mathbb Z$, so it is saturated.
--
--   The cores $P_{m+1}$ give the refutation for $m\ge6$. The statement concerns schedules over $\mathbb Z$ only: one-sided schedules of $P_n$ can have free days (Remark 2.5).
--
--   Differences from the source: none.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma 2.4, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable
import Definitions.Def_PinwheelDensity_ExactRange_coreP

namespace PinwheelDensity.ExactRange

/-- Lemma 2.4 (Saturation), p. 4: no schedule of `Pₙ` over `ℤ` has a free day, `Pₙ` is schedulable,
and so it is saturated. The statement concerns schedules over `ℤ` only (Remark 2.5, p. 5). -/
theorem lemma_2_4 (n : ℕ) (hn : 3 ≤ n) :
    NoScheduleWithFreeDay (coreP n) ∧ ZSchedulable (coreP n) ∧ Saturated (coreP n) := by sorry

end PinwheelDensity.ExactRange
