-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_interp_u_boundaries_v1
-- name    : TarchaBraids.thm_3_15_right_interp_u_boundaries_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T12:08:26.74537+00:00
-- url     : https://prove2.me/theorems/813aaea5-bd01-4366-b631-67b2c987f02c
-- title:
--   Tarcha 3.15 right interpolation has the required u-boundaries
-- statement:
--   At interpolation parameter u=0 the right interpolation is the right braid-word path, and at u=1 it is the common outer-rotation path.
-- source:
--   Modular boundary layer for Tarcha's explicit adjacent Artin relation homotopy.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_config_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_interp_u_boundaries_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ q : unitInterval,
        configProj n (rightOuterInterpConfig i j hji 0 q) =
          configProj n (rightBraidConfig n i j (q : ℝ))) ∧
      (∀ (hi2 : (i : ℕ) + 2 < n) (q : unitInterval),
        configProj n (rightOuterInterpConfig i j hji 1 q) =
          configProj n (outerRotateConfig i hi2 (q : ℝ))) := by sorry

end TarchaBraids
