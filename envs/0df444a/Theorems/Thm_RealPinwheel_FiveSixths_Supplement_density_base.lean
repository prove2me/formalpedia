-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_Supplement_density_base
-- name    : RealPinwheel.FiveSixths.Supplement.density_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:33.047658+00:00
-- url     : https://prove2.me/theorems/12ae659c-0ead-429a-8373-39ea39cdc6e4
-- title:
--   Lemma 11 (used in the proof of Theorem 4) — density base through nine tasks
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a nonempty ordered real-period instance with $1\le a_1\le\cdots\le a_n$. Periods may be irrational, and equal periods label distinct tasks. Write $D(A)=\sum_{i=1}^n1/a_i$ for density and $P(A)=\sum_{i=1}^{n-1}1/a_i$ for potential. Schedulability means that a single schedule assigns exactly one task to each day and, for every task $i$, positive integer $\ell$ and starting day $m\ge0$, executes $i$ at least $\ell$ times in $[m,m+\lceil\ell a_i\rceil)$.
--
--   If $n\le9$, $a_1\ge4$ and $D(A)\le17/20$, then
--
--   $$\operatorname{Schedulable}(A).$$
--
--   This is the density base case supporting Theorem 4, including every nonempty dimension from one through nine and equality at both bounds.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 11, printed p. 11 (PDF p. 12); proof printed p. 12 (PDF p. 13)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths.Supplement

/-- Lemma 11, printed p. 11 (PDF p. 12); proof printed p. 12 (PDF p. 13).
The first position is the minimum period because Instance includes monotonicity. -/
theorem density_base {n : ℕ} (A : Instance n) (hn : n ≤ 9)
    (hmin : 4 ≤ A.period ⟨0, A.positive_dimension⟩)
    (hD : density A ≤ (17 : ℝ) / 20) :
    Schedulable A.period := by sorry

end RealPinwheel.FiveSixths.Supplement
