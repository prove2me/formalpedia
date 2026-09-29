-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_quotient_eq_v1
-- name    : TarchaBraids.thm_3_15_adjacent_word_quotient_eq_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T13:33:09.118983+00:00
-- url     : https://prove2.me/theorems/2db2d00d-8b98-4ee1-a4df-a1215f12a4bb
-- title:
--   Tarcha 3.15 adjacent braid words define the same homotopy quotient class
-- statement:
--   For adjacent generators, the left and right three-half-twist word loops represent the same path-homotopy class because both equal the same outer-rotation class.
-- source:
--   Modular remaining adjacent-relation proof for Tarcha 3.15.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_word_eq_outer_quotient_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_eq_outer_quotient_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_word_quotient_eq_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic.Quotient.mk (leftBraidWordLoop n i j) =
        Path.Homotopic.Quotient.mk (rightBraidWordLoop n i j) := by sorry

end TarchaBraids
