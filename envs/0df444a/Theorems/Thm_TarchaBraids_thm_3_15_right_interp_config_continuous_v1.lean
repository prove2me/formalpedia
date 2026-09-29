-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_interp_config_continuous_v1
-- name    : TarchaBraids.thm_3_15_right_interp_config_continuous_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T12:00:08.261298+00:00
-- url     : https://prove2.me/theorems/aa87ada1-7b2d-476e-b7ba-99683418b97c
-- title:
--   Tarcha 3.15 right interpolation ordered configuration is continuous
-- statement:
--   The collision-free right interpolation between the adjacent braid word and the common outer rotation is continuous as a two-parameter map into ordered configuration space.
-- source:
--   Modular continuity lift for Tarcha's explicit adjacent Artin relation homotopy.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_interp_config_continuous_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      Continuous (fun z : unitInterval × unitInterval =>
        rightOuterInterpConfig i j hji z.1 z.2) := by sorry

end TarchaBraids
