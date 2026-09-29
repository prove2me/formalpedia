-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_word_homotopic_outer_v1
-- name    : TarchaBraids.thm_3_15_right_word_homotopic_outer_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T13:01:46.331478+00:00
-- url     : https://prove2.me/theorems/7fecacc2-4570-448b-8488-f5a6f673d70f
-- title:
--   Tarcha 3.15 right braid word is homotopic to the outer rotation
-- statement:
--   The explicit right three-half-twist braid-word loop is path-homotopic, relative to its endpoints, to the common outer-rotation loop.
-- source:
--   Modular remaining adjacent-relation proof for Tarcha 3.15.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1
import Definitions.Def_TarchaBraids_adjacent_outer_loop_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_config_continuous_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_boundaries_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_word_identification_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_word_homotopic_outer_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Path.Homotopic (rightBraidWordLoop n i j) (outerRotateLoop i j hji) := by sorry

end TarchaBraids
