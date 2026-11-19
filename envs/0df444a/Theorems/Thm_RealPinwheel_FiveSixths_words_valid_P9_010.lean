-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010
-- name    : RealPinwheel.FiveSixths.words_valid_P9_010
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T05:44:09.552754+00:00
-- url     : https://prove2.me/theorems/31e897cc-f791-4239-9036-4dac3e0c458d
-- title:
--   Validity of annotated word subfamily P9 11
-- statement:
--   Let $A$ be a real-period instance with 9 tasks, and let $j$ be a source word index with $2070\le j<2558$. If the reciprocal-period vector of $A$ belongs to this word's annotated box, then there is a valid periodic schedule whose positive period satisfies
--
--   $$L\le 1800.$$
--
--   All starting days and all positive multiplicities are included in validity. This word-validity assertion is independent of the separate density or potential domain coverage theorem.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family P9, entries 2071–2558.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_P9_010 (A : Instance 9) (j : Fin 7968)
    (hlo : 2070 ≤ j.val) (hhi : j.val < 2558)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
