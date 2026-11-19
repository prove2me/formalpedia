-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_bounded_density_base
-- name    : RealPinwheel.FiveSixths.bounded_density_base
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:50:36.019796+00:00
-- url     : https://prove2.me/theorems/935c3d78-571a-490e-a4ae-d629a4c29622
-- title:
--   Bounded periodic density base through eight tasks
-- statement:
--   Let $A$ be a nonempty ordered real-period instance of dimension $n\le8$, with all periods at least one. If its density satisfies $D(A)\le5/6$, then it admits a valid periodic schedule with a positive integer period $L$ satisfying
--
--   $$L<4\cdot2^n.$$
--
--   Validity requires every task to occur at least $\ell$ times in every window of $\lceil\ell a_i\rceil$ days, for every positive integer $\ell$. This is the bounded periodic form of Lemma 5 supplied by the certificate families and Table 1; it retains the witnesses needed in Theorem 3.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, A Simple Computer-Assisted Proof of the 5/6-Bound for Real-Period Pinwheel Scheduling, STOC 2027 submission #885, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Lemma 5 and Section 4, Table 1, printed pp. 10–11 (PDF pp. 11–12)

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.bounded_density_base {n : ℕ} (A : Instance n) (hn : n ≤ 8)
    (hD : density A ≤ (5 : ℝ) / 6) :
    ∃ (L : ℕ) (S : ℕ → Fin n), 0 < L ∧ L < 4 * 2 ^ n ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
