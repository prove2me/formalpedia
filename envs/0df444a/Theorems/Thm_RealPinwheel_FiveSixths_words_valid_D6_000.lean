-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D6_000
-- name    : RealPinwheel.FiveSixths.words_valid_D6_000
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:38:26.881298+00:00
-- url     : https://prove2.me/theorems/ed2cbf51-3102-43c6-944f-3a008de6625c
-- title:
--   Validity of annotated words W_D6_000
-- statement:
--   Let $A$ be a real-period instance with 6 tasks. Choose an annotated word of source family D6, with zero-based index $j$ in the interval from 0 inclusive to 630 exclusive. If the vector of reciprocal periods belongs to this word's annotated box, then $A$ admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 64.$$
--
--   This proves the validity half of the finite certificate for these words, independently of any density-domain coverage assertion. All multiplicities and all starting days are included.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D6, entries 1–630.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD6
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D6_000 (A : Instance 6) (j : Fin 630)
    (hlo : 0 ≤ j.val) (hhi : j.val < 630)
    (hb : codeBox (codeFunctionD6 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 6), 0 < L ∧ L ≤ 64 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
