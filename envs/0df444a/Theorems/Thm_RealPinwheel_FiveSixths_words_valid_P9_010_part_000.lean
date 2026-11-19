-- Prove2me | Theorems.Thm_RealPinwheel_FiveSixths_words_valid_P9_010_part_000
-- name    : RealPinwheel.FiveSixths.words_valid_P9_010_part_000
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T10:52:25.728634+00:00
-- url     : https://prove2.me/theorems/3d8d91de-d521-4ddc-b59c-52943f081a42
-- title:
--   Validity of annotated words W_P9_010_parts_000
-- statement:
--   Let $A$ be a real-period instance with 9 tasks. Choose an annotated word of source family P9, with zero-based index $j$ in the interval from 2070 inclusive to 2185 exclusive. If the vector of reciprocal periods belongs to this word's annotated box, then $A$ admits a valid periodic schedule with positive period $L$ satisfying
--
--   $$L\le 1800.$$
--
--   This proves the validity half of the finite certificate for these words, independently of any density-domain coverage assertion. All multiplicities and all starting days are included.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Family P9, entries 2071–2185.

import Definitions.Def_RealPinwheel_FiveSixths_CodeFunctionP9
open RealPinwheel.FiveSixths

theorem RealPinwheel.FiveSixths.words_valid_P9_010_part_000 (A : Instance 9) (j : Fin 7968)
    (hlo : 2070 ≤ j.val) (hhi : j.val < 2185)
    (hb : codeBox (codeFunctionP9 j.val) (fun i => 1 / A.period i)) :
    ∃ (L : ℕ) (S : ℕ → Fin 9), 0 < L ∧ L ≤ 1800 ∧
      (∀ t, S (t + L) = S t) ∧ Valid A.period S := by sorry
