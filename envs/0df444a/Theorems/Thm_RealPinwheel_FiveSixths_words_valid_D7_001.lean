-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D7_001
-- name    : RealPinwheel.FiveSixths.words_valid_D7_001
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T04:43:13.263099+00:00
-- url     : https://prove2.me/theorems/6f5a3885-a121-431e-9b8e-48bc21ee910b
-- title:
--   Validity of annotated words W_D7_001
-- statement:
--   Let $A$ be a real-period instance with 7 tasks. Choose an annotated word of source family D7, with zero-based index $j$ in the interval from 196 inclusive to 558 exclusive. If the vector of reciprocal periods belongs to this word's annotated box, then $A$ admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 352.$$
--
--   This proves the validity half of the finite certificate for these words, independently of any density-domain coverage assertion. All multiplicities and all starting days are included.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D7, entries 197–558.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD7
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D7_001 (A : Instance 7) (j : Fin 1657)
    (hlo : 196 ≤ j.val) (hhi : j.val < 558)
    (hb : codeBox (codeFunctionD7 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 7), 0 < L ∧ L ≤ 352 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
