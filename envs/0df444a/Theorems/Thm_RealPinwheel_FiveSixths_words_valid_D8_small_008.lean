-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_008
-- name    : RealPinwheel.FiveSixths.words_valid_D8_small_008
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-18T05:19:38.930484+00:00
-- url     : https://prove2.me/theorems/55cc2c1c-691f-4e5e-9d71-04bd1222838a
-- title:
--   Validity of eight-task word subfamily 9
-- statement:
--   Let $A$ be an eight-task real-period instance, and let $j$ be a zero-based source word index with $1464\le j<1816$. If the vector of reciprocal periods belongs to the annotated box of word $j$, then $A$ admits a valid periodic schedule with positive period bounded by
--
--   $$L\le608.$$
--
--   This is the word-validity assertion for the designated subfamily. It includes every starting day and every positive multiplicity, independently of any density-domain coverage claim.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D8, entries 1465–1816.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D8_small_008 (A : Instance 8) (j : Fin 3725)
    (hlo : 1464 ≤ j.val) (hhi : j.val < 1816)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
