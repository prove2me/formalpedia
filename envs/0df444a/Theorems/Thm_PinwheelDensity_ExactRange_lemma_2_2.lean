-- Prove2me | Theorems.Thm_PinwheelDensity_ExactRange_lemma_2_2
-- name    : PinwheelDensity.ExactRange.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:48.017206+00:00
-- url     : https://prove2.me/theorems/e08b4ab0-1fed-49fb-be50-befb39828148
-- title:
--   Lemma 2.2 — idle days force a large period sum
-- statement:
--   Let positive integer periods $a_1,\dots,a_k$ be served by a schedule over $\mathbb Z$, and let $d$ be a day on which none of the $k$ tasks is executed. Then
--   $$\sum_i a_i\ge k(k+1).$$
--
--   This is the counting bound that makes the cores $(m,(m+1)^{[m-1]})$ free of free days, and so proves the sharpness of $c(m)$.
--
--   Differences from the source: none.
-- source:
--   Cihangir Dogukan Arisan, STOC 2027 submission #387 (October 2026), Lemma 2.2, p. 4 (PDF p. 4)

import Mathlib
import Definitions.Def_PinwheelDensity_ExactRange_Schedulable

namespace PinwheelDensity.ExactRange

/-- Lemma 2.2 (Idle days), p. 4: if a schedule over `ℤ` of `k` positive integer periods has a free
day, then the periods sum to at least `k (k + 1)`. -/
theorem lemma_2_2 (A : List ℕ) (hA : ∀ a ∈ A, 1 ≤ a) (σ : ZSchedule A) (d : ℤ)
    (hd : σ.IsFreeDay d) : A.length * (A.length + 1) ≤ A.sum := by sorry

end PinwheelDensity.ExactRange
