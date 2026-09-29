-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_interp_boundaries_v1
-- name    : TarchaBraids.thm_3_15_right_interp_boundaries_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T12:57:10.146406+00:00
-- url     : https://prove2.me/theorems/6f25397f-ed95-49a9-a843-89b677754020
-- title:
--   Tarcha 3.15 right interpolation has the required homotopy boundaries
-- statement:
--   The right interpolation square starts at the adjacent right braid-word path, ends at the common outer-rotation path, and keeps both time endpoints at the unordered base configuration.
-- source:
--   Modular boundary layer for Tarcha's explicit right adjacent Artin relation homotopy.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_interp_boundaries_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : unitInterval,
        configProj n (rightOuterInterpConfig i j hji 0 q) =
          configProj n (rightBraidConfig n i j (q : ℝ))) ∧
      (∀ (hi2 : (i : ℕ) + 2 < n) (q : unitInterval),
        configProj n (rightOuterInterpConfig i j hji 1 q) =
          configProj n (outerRotateConfig i hi2 (q : ℝ))) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 0) = baseUnordered n) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 1) = baseUnordered n) := by sorry

end TarchaBraids
