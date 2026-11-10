-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_potential_reduction
-- name    : RealPinwheel.FiveSixths.potential_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:19.540514+00:00
-- url     : https://prove2.me/theorems/8706021e-0b3a-4a23-93ad-522bf48aefdb
-- title:
--   Lemma 7 — potential-preserving reduction to nine tasks
-- statement:
--   Let $A$ be a real-period instance of dimension $n\ge9$ and let $P(A)$ be the sum of all task densities except the last, smallest density. If $P(A)\le5/6$, then
--
--   $$\exists B\text{ of dimension }9:\quad P(B)\le\frac56\ \land\ \bigl(\operatorname{Schedulable}(B)\Rightarrow\operatorname{Schedulable}(A)\bigr).$$
--
--   The witness $B$ is itself a nonempty ordered instance with arbitrary real periods at least one. The assumption concerns potential rather than total density. This is the source's schedulability reduction; the additional quantitative periodicity facts used for the final goal remain proof obligations rather than hypotheses or added conclusions of this milestone.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 7, printed p. 3 (PDF p. 4); proof printed pp. 6–7 (PDF pp. 7–8)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Lemma 7, printed p. 3 (PDF p. 4), proof printed pp. 6-7 (PDF pp. 7-8). -/
theorem potential_reduction {n : ℕ} (A : Instance n) (hn : 9 ≤ n)
    (hP : potential A ≤ (5 : ℝ) / 6) :
    ∃ B : Instance 9, potential B ≤ (5 : ℝ) / 6 ∧
      (Schedulable B.period → Schedulable A.period) := by sorry

end RealPinwheel.FiveSixths
