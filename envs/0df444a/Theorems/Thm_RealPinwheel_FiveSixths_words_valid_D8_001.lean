-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_001
-- name    : RealPinwheel.FiveSixths.words_valid_D8_001
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T04:41:38.40421+00:00
-- url     : https://prove2.me/theorems/9846581f-0569-48b8-963f-a3ce9881e80c
-- title:
--   Validity of annotated words W_D8_001
-- statement:
--   Let $A$ be a real-period instance with 8 tasks. Choose an annotated word of source family D8, with zero-based index $j$ in the interval from 2228 inclusive to 3725 exclusive. If the vector of reciprocal periods belongs to this word's annotated box, then $A$ admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 608.$$
--
--   This proves the validity half of the finite certificate for these words, independently of any density-domain coverage assertion. All multiplicities and all starting days are included.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D8, entries 2229–3725.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D8_001 (A : Instance 8) (j : Fin 3725)
    (hlo : 2228 ≤ j.val) (hhi : j.val < 3725)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
