-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_007
-- name    : RealPinwheel.FiveSixths.words_valid_D8_small_007
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T05:16:59.938851+00:00
-- url     : https://prove2.me/theorems/6bfee9e8-a1db-4a3a-8b8d-eca6c08a0183
-- title:
--   Validity of eight-task word subfamily 8
-- statement:
--   Let $A$ be an eight-task real-period instance, and let $j$ be a zero-based source word index with $1157\le j<1464$. If the vector of reciprocal periods belongs to the annotated box of word $j$, then $A$ admits a valid periodic schedule with positive period bounded by
--
--   $$L\le608.$$
--
--   This is the word-validity assertion for the designated subfamily. It includes every starting day and every positive multiplicity, independently of any density-domain coverage claim.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D8, entries 1158–1464.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D8_small_007 (A : Instance 8) (j : Fin 3725)
    (hlo : 1157 ≤ j.val) (hhi : j.val < 1464)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
