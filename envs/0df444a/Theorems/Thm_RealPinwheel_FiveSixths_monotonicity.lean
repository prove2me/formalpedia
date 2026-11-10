-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_monotonicity
-- name    : RealPinwheel.FiveSixths.monotonicity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:36:13.184812+00:00
-- url     : https://prove2.me/theorems/54c74643-258a-4796-a747-888bbdd6fc76
-- title:
--   Lemma 8 — period monotonicity
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a real-period instance and let $S$ be a valid schedule for it. Choose a task $j$ and a real number $b\ge a_j$. Replacing only its period gives a labelled vector $a'$ with
--
--   $$a'_j=b,\quad a'_i=a_i\ (i\ne j),\qquad \operatorname{Valid}(a,S)\Longrightarrow\operatorname{Valid}(a',S).$$
--
--   The very same schedule remains valid, with every task label unchanged. This is the coordinate monotonicity underlying domination by periodic schedules. The replacement vector need not be sorted; a later reordering permutes schedule labels as described immediately after the source lemma.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 8, printed p. 3 (PDF p. 4)

import Definitions.Def_RealPinwheel_FiveSixths_Transformations

namespace RealPinwheel.FiveSixths

/-- Lemma 8, printed p. 3 (PDF p. 4). Labels are unchanged after replacement. -/
theorem monotonicity {n : ℕ} (A : Instance n) (S : ℕ → Fin n)
    (hS : Valid A.period S) (j : Fin n) (b : ℝ) (hb : A.period j ≤ b) :
    Valid (replacePeriod A.period j b) S := by sorry

end RealPinwheel.FiveSixths
