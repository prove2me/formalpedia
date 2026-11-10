-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_density_base
-- name    : RealPinwheel.FiveSixths.density_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:13.02567+00:00
-- url     : https://prove2.me/theorems/58c8b421-7efb-4c3b-af9c-34605b4582dd
-- title:
--   Lemma 5 — density base cases through eight tasks
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a real-period instance with $1\le n\le8$, and write $D(A)=\sum_i1/a_i$. Then
--
--   $$D(A)\le\frac56\quad\Longrightarrow\quad\exists S:\ \operatorname{Valid}(A,S).$$
--
--   Validity quantifies over every task, every positive multiplicity and every window start. This supplies the small-dimension density cases, including equality at the density boundary. No certificate acceptance or coverage hypothesis is imposed.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 5, printed p. 2 (PDF p. 3); repeated printed p. 10 (PDF p. 11), proof printed p. 11 (PDF p. 12)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Lemma 5, printed p. 2 (PDF p. 3), repeated printed p. 10 (PDF p. 11). -/
theorem density_base {n : ℕ} (A : Instance n) (hn : n ≤ 8)
    (hD : density A ≤ (5 : ℝ) / 6) : Schedulable A.period := by sorry

end RealPinwheel.FiveSixths
