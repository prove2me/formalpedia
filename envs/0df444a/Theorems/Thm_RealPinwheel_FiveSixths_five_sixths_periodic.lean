-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_five_sixths_periodic
-- name    : RealPinwheel.FiveSixths.five_sixths_periodic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:35:14.1383+00:00
-- url     : https://prove2.me/theorems/84bc66bc-bfe2-4acb-8e57-8b8d1c42f46c
-- title:
--   Theorem 3 — real-period five-sixths bound with bounded period
-- statement:
--   Let $A=(a_1,\ldots,a_n)$ be any nonempty real-period pinwheel instance with $1\le a_1\le\cdots\le a_n$. The periods may be irrational and repeated period values still label distinct tasks. If $D(A)=\sum_i1/a_i\le5/6$, then there exist a positive integer $L$ and a schedule $S$ assigning exactly one task to each day such that
--
--   $$L<4\cdot2^n,\qquad\forall t\ge0,\ S(t+L)=S(t),$$
--
--   and
--
--   $$\forall i,\ \forall\ell\ge1,\ \forall m\ge0,\quad\#\{t\in[m,m+\lceil\ell a_i\rceil):S(t)=i\}\ge\ell.$$
--
--   The integer $L$ is a period of the schedule and need not be its least period. The result supplies both a valid infinite schedule and a strict dimension-dependent bound on a finite word representing it. Neither conclusion is conditional on certificate data.
--
--   Differences from the source:
--   - encoding: positive days and task labels 1 through n → natural days starting at zero and task positions Fin n; reason: day t encodes source day t+1 and position i encodes source task i+1; all windows and distinct task identities are preserved
-- source:
--   Hiroshi Fujiwara, Grzegorz Gutowski, Katsuhisa Ouchi, Alexander Wolff, STOC 2027 submission #885 (October 2026), Theorem 3, printed p. 2 (PDF p. 3); proof printed p. 11 (PDF p. 12)

import Definitions.Def_RealPinwheel_FiveSixths_Instance

namespace RealPinwheel.FiveSixths

/-- Theorem 3, printed p. 2 (PDF p. 3); proof printed p. 11 (PDF p. 12).
The length is a positive period, not necessarily the least one. -/
theorem five_sixths_periodic {n : ℕ} (A : Instance n)
    (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin n),
      0 < L ∧ L < 4 * 2 ^ n ∧
      (∀ t : ℕ, S (t + L) = S t) ∧ Valid A.period S := by sorry

end RealPinwheel.FiveSixths
