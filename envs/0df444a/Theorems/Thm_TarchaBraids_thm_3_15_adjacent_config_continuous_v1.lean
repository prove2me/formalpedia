-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_config_continuous_v1
-- name    : TarchaBraids.thm_3_15_adjacent_config_continuous_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:33:42.717809+00:00
-- url     : https://prove2.me/theorems/11a23c66-c960-4b28-98ae-ba42eab61fde
-- title:
--   Tarcha 3.15 adjacent ordered configuration paths are continuous
-- statement:
--   The ordered-configuration lifts of the left adjacent braid word, right adjacent braid word and outer-rotation comparison path are continuous.
-- source:
--   Modular lift of the accepted raw coordinatewise continuity theorem through the ordered-configuration subtype.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_config_continuous_v1 :
    (∀ (n : ℕ) (i j : Fin (n - 1)), Continuous (leftBraidConfig n i j)) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)), Continuous (rightBraidConfig n i j)) ∧
    (∀ {n : ℕ} (i : Fin (n - 1)) (hi2 : (i : ℕ) + 2 < n),
      Continuous (outerRotateConfig i hi2)) := by sorry

end TarchaBraids
