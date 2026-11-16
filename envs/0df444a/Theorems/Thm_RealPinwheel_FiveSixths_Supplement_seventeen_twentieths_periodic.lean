-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_Supplement_seventeen_twentieths_periodic
-- name    : RealPinwheel.FiveSixths.Supplement.seventeen_twentieths_periodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:21:58.862195+00:00
-- url     : https://prove2.me/theorems/31351b57-c68b-4c7f-b00e-556385ff75c2
-- title:
--   Theorem 4 (companion theorem; not used in the proof of the goal) — real-period 17/20 bound with bounded period
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be a nonempty ordered real-period instance with $1\le a_1\le\cdots\le a_n$. Periods may be irrational, and equal periods label distinct tasks. Write $D(A)=\sum_{i=1}^n1/a_i$ for density and $P(A)=\sum_{i=1}^{n-1}1/a_i$ for potential. Schedulability means that a single schedule assigns exactly one task to each day and, for every task $i$, positive integer $\ell$ and starting day $m\ge0$, executes $i$ at least $\ell$ times in $[m,m+\lceil\ell a_i\rceil)$.
--
--   If $a_1\ge4$ and $D(A)\le17/20$, then there exist a positive integer $L$ and a schedule $S:\mathbb N\to\{1,\ldots,n\}$ such that
--
--   $$0<L<19\cdot2^n,\qquad\forall t\ge0,\ S(t+L)=S(t),$$
--
--   and
--
--   $$\forall i,\ \forall\ell\ge1,\ \forall m\ge0,\quad\#\{t\in[m,m+\lceil\ell a_i\rceil):S(t)=i\}\ge\ell.$$
--
--   The integer $L$ is a period and need not be the least period. This companion theorem extends the density guarantee for instances whose minimum period is at least four; it is not used in the proof of the published goal Theorem 3. The schedule, validity and strict length bound are unconditional conclusions, including irrational periods and equality in the density bound.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Theorem 4, printed p. 2 (PDF p. 3); proof printed p. 12 (PDF p. 13)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths.Supplement

/-- Theorem 4, printed p. 2 (PDF p. 3); proof printed p. 12 (PDF p. 13).
The positive integer L is a period, not necessarily the least period.
No finite-covering or periodic-witness hypothesis is assumed. -/
theorem seventeen_twentieths_periodic {n : ℕ} (A : Instance n)
    (hmin : 4 ≤ A.period ⟨0, A.positive_dimension⟩)
    (hD : density A ≤ (17 : ℝ) / 20) :
    ∃ (L : ℕ) (S : ℕ → Fin n),
      0 < L ∧ L < 19 * 2 ^ n ∧
      (∀ t : ℕ, S (t + L) = S t) ∧ Valid A.period S := by sorry

end RealPinwheel.FiveSixths.Supplement
