-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_left_word_eq_outer_quotient_v1
-- name    : TarchaBraids.thm_3_15_left_word_eq_outer_quotient_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T11:04:05.937587+00:00
-- url     : https://prove2.me/theorems/7d9b696e-819d-40d0-97ae-4d376fc2fbff
-- title:
--   Tarcha 3.15 left braid word equals the common outer loop in the fundamental group quotient
-- statement:
--   The left adjacent three-half-twist word loop is homotopic relative endpoints to the common outer-rotation loop.
-- source:
--   Modular homotopy quotient layer for Tarcha's adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_left_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Definitions.Def_TarchaBraids_adjacent_outer_loop_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_interp_config_continuous_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_interp_boundaries_v1
import Theorems.Thm_TarchaBraids_thm_3_15_left_word_identification_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_left_word_eq_outer_quotient_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic.Quotient.mk (leftBraidWordLoop n i j) =
        Path.Homotopic.Quotient.mk (outerRotateLoop i j hji) := by sorry

end TarchaBraids
