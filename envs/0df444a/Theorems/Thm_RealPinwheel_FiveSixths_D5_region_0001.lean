-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_D5_region_0001
-- name    : RealPinwheel.FiveSixths.D5_region_0001
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:10:27.908203+00:00
-- url     : https://prove2.me/theorems/cc513034-0077-4cab-9a5c-61fdec7ac2cd
-- title:
--   Finite coverage region D5_region_0001
-- statement:
--   Let $A$ be an ordered 5-task real-period instance with periods at least one, and let $d_i=1/a_i$. Suppose its density is at most $5/6$ and its density coordinates satisfy
--
--   $$d_{1}>\frac{3}{14},\quad d_{1}\le\frac{5}{14}.$$
--
--   Then it admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 32.$$
--
--   This is a restricted part of the finite real-domain coverage in the source. The coordinate restrictions partition that domain in the reduction; they are not additional assumptions of the mission theorem.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. The domain inclusion of equation (3), restricted to the displayed coordinate region; query (5) for P9 or query (4) for D1–D8.

import Theorems.Thm_RealPinwheel_FiveSixths_witnessCheck_sound
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_000
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_001
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_002
import Theorems.Thm_RealPinwheel_FiveSixths_checked_D5_003
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.D5_region_0001 (A : Instance 5) (hD : density A ≤ (5 : ℝ) / 6)
    (r0 : ¬ (1 / A.period 0 ≤ (3 : ℝ) / 14))
    (r1 : 1 / A.period 0 ≤ (5 : ℝ) / 14)
    : ∃ (L : ℕ) (S : ℕ → Fin 5), 0 < L ∧ L ≤ 32 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
