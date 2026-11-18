-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_bounded_folding
-- name    : RealPinwheel.FiveSixths.bounded_folding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:50:38.463267+00:00
-- url     : https://prove2.me/theorems/7e2ac09e-e1e3-42d2-9131-70f0d9252737
-- title:
--   Potential-preserving fold with periodic schedule lifting
-- statement:
--   Let $A$ be an ordered real-period instance of dimension $r+2\ge10$, with all periods at least one and potential $P(A)\le5/6$. There exists an ordered instance $B$ of dimension $r+1$, again with periods at least one, satisfying $P(B)\le5/6$, such that every valid periodic schedule of $B$ with positive period $L$ yields a valid schedule of $A$ with period
--
--   $$2L.$$
--
--   The period need not be least. This is the one-step folding assertion and its periodic lifting from Section 2. Iteration reduces the dimension to nine while keeping an explicit bound on the final period. The exact period $2L$ is permitted even when a shorter period would suffice.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, A Simple Computer-Assisted Proof of the 5/6-Bound for Real-Period Pinwheel Scheduling, STOC 2027 submission #885, October 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf, Section 2, proof of Lemma 7, equation (1) and periodic unfolding paragraph, printed pp. 6–7 (PDF pp. 7–8)

import Definitions.Def_RealPinwheel_FiveSixths_Instance
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.bounded_folding {r : ℕ} (A : Instance (r + 2)) (hr : 9 ≤ r + 1)
    (hP : potential A ≤ (5 : ℝ) / 6) :
    ∃ B : Instance (r + 1), potential B ≤ (5 : ℝ) / 6 ∧
      ∀ (L : ℕ) (S : ℕ → Fin (r + 1)), Periodic S L → Valid B.period S →
        ∃ T : ℕ → Fin (r + 2), Periodic T (2 * L) ∧ Valid A.period T := by sorry
