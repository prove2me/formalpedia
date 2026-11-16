-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_Supplement_potential_reduction
-- name    : RealPinwheel.FiveSixths.Supplement.potential_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:26.560255+00:00
-- url     : https://prove2.me/theorems/2d0e67f4-b24d-4b36-8850-c0e8419e7a01
-- title:
--   Lemma 13 (used in the proof of Theorem 4) — reduction to ten tasks
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a nonempty ordered real-period instance with $1\le a_1\le\cdots\le a_n$. Periods may be irrational, and equal periods label distinct tasks. Write $D(A)=\sum_{i=1}^n1/a_i$ for density and $P(A)=\sum_{i=1}^{n-1}1/a_i$ for potential. Schedulability means that a single schedule assigns exactly one task to each day and, for every task $i$, positive integer $\ell$ and starting day $m\ge0$, executes $i$ at least $\ell$ times in $[m,m+\lceil\ell a_i\rceil)$.
--
--   If $n\ge10$, $a_1\ge4$ and $P(A)\le17/20$, then there exists an ordered real-period instance $B=(b_1,\ldots,b_{10})$ such that
--
--   $$b_1\ge4,\qquad P(B)\le\frac{17}{20},\qquad\operatorname{Schedulable}(B)\Longrightarrow\operatorname{Schedulable}(A).$$
--
--   The witness has exactly ten tasks. This reduction supports Theorem 4 and includes $n=10$, where $B=A$ is permitted. It asserts ordinary schedulability transfer; the quantitative period control for Theorem 4 remains an additional proof obligation.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Lemma 13, printed p. 11 (PDF p. 12); proof printed p. 12 (PDF p. 13)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths.Supplement

/-- Lemma 13, printed p. 11 (PDF p. 12); proof printed p. 12 (PDF p. 13).
The ten-task witness retains both the minimum-period and potential bounds. -/
theorem potential_reduction {n : ℕ} (A : Instance n) (hn : 10 ≤ n)
    (hmin : 4 ≤ A.period ⟨0, A.positive_dimension⟩)
    (hP : potential A ≤ (17 : ℝ) / 20) :
    ∃ B : Instance 10,
      4 ≤ B.period ⟨0, B.positive_dimension⟩ ∧
      potential B ≤ (17 : ℝ) / 20 ∧
      (Schedulable B.period → Schedulable A.period) := by sorry

end RealPinwheel.FiveSixths.Supplement
