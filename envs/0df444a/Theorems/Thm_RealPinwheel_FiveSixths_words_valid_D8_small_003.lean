-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_D8_small_003
-- name    : RealPinwheel.FiveSixths.words_valid_D8_small_003
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:12:33.401334+00:00
-- url     : https://prove2.me/theorems/fc6d581f-a7f1-437b-b21e-c0f20e5803de
-- title:
--   Validity of eight-task word subfamily 4
-- statement:
--   Let $A$ be an eight-task real-period instance, and let $j$ be a zero-based source word index with $287\le j<458$. If the vector of reciprocal periods belongs to the annotated box of word $j$, then $A$ admits a valid periodic schedule with positive period bounded by
--
--   $$L\le608.$$
--
--   This is the word-validity assertion for the designated subfamily. It includes every starting day and every positive multiplicity, independently of any density-domain coverage claim.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family D8, entries 288–458.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionD8
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_D8_small_003 (A : Instance 8) (j : Fin 3725)
    (hlo : 287 ≤ j.val) (hhi : j.val < 458)
    (hb : codeBox (codeFunctionD8 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 8), 0 < L ∧ L ≤ 608 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
