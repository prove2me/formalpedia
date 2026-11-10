-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_potential_base
-- name    : RealPinwheel.FiveSixths.potential_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:08.926734+00:00
-- url     : https://prove2.me/theorems/8bbe6255-3311-4751-a827-bbf10a100343
-- title:
--   Lemma 6 — nine-task potential base case
-- statement:
--   Let $A=(a_1,\ldots,a_9)$ be an ordered real-period instance, with every $a_i\ge1$, and let $P(A)=\sum_{i=1}^8 1/a_i$. Then
--
--   $$P(A)\le\frac56\quad\Longrightarrow\quad\exists S:\ \operatorname{Valid}(A,S).$$
--
--   This covers the full nine-task potential domain, not only instances whose total density is at most $5/6$. Its total density may reach $15/16$. The conclusion requires all real-period windows, with no assumption that an external verifier succeeds.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 6, printed p. 2 (PDF p. 3); repeated and proved printed p. 11 (PDF p. 12)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Lemma 6, printed p. 2 (PDF p. 3), repeated printed p. 11 (PDF p. 12). -/
theorem potential_base (A : Instance 9) (hP : potential A ≤ (5 : ℝ) / 6) :
    Schedulable A.period := by sorry

end RealPinwheel.FiveSixths
