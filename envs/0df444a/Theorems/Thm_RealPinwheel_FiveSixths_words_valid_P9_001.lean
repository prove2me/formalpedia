-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_001
-- name    : RealPinwheel.FiveSixths.words_valid_P9_001
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:02:48.531198+00:00
-- url     : https://prove2.me/theorems/55d0b753-f523-4160-916a-995a1efb03a4
-- title:
--   Validity of annotated words W_P9_001
-- statement:
--   Let $A$ be a real-period instance with 9 tasks. Choose an annotated word of source family P9, with zero-based index $j$ in the interval from 32 inclusive to 113 exclusive. If the vector of reciprocal periods belongs to this word's annotated box, then $A$ admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 1800.$$
--
--   This proves the validity half of the finite certificate for these words, independently of any density-domain coverage assertion. All multiplicities and all starting days are included.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family P9, entries 33–113.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_P9_001 (A : Instance 9) (j : Fin 7968)
    (hlo : 32 ≤ j.val) (hhi : j.val < 113)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
