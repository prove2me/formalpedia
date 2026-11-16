-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_Supplement_potential_base
-- name    : RealPinwheel.FiveSixths.Supplement.potential_base
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:20:58.016146+00:00
-- url     : https://prove2.me/theorems/937641e2-b58f-44e8-9310-de786486e3a2
-- title:
--   Lemma 12 (used in the proof of Theorem 4) — ten-task potential base
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a nonempty ordered real-period instance with $1\le a_1\le\cdots\le a_n$. Periods may be irrational, and equal periods label distinct tasks. Write $D(A)=\sum_{i=1}^n1/a_i$ for density and $P(A)=\sum_{i=1}^{n-1}1/a_i$ for potential. Schedulability means that a single schedule assigns exactly one task to each day and, for every task $i$, positive integer $\ell$ and starting day $m\ge0$, executes $i$ at least $\ell$ times in $[m,m+\lceil\ell a_i\rceil)$.
--
--   In dimension $n=10$, if $a_1\ge4$ and $P(A)\le17/20$, then
--
--   $$\operatorname{Schedulable}(A).$$
--
--   This is the full ten-task potential base case supporting Theorem 4. Potential omits only the final task's density; the hypothesis is not a bound on total density. The conclusion covers both branches of Appendix A and their equality boundaries, without any certificate or branch hypothesis.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 12, printed p. 11 (PDF p. 12); proof printed p. 16 (PDF p. 17)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths.Supplement

/-- Lemma 12, printed p. 11 (PDF p. 12); repeated and proved in Appendix A,
printed p. 16 (PDF p. 17). Covers the entire ten-task potential domain. -/
theorem potential_base (A : Instance 10)
    (hmin : 4 ≤ A.period ⟨0, A.positive_dimension⟩)
    (hP : potential A ≤ (17 : ℝ) / 20) :
    Schedulable A.period := by sorry

end RealPinwheel.FiveSixths.Supplement
