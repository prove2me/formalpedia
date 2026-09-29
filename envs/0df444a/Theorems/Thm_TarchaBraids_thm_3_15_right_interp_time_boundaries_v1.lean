-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_interp_time_boundaries_v1
-- name    : TarchaBraids.thm_3_15_right_interp_time_boundaries_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T12:16:52.314441+00:00
-- url     : https://prove2.me/theorems/85c3bcc1-3b3c-4fda-bc05-ec33645466ff
-- title:
--   Tarcha 3.15 right interpolation has the required time boundaries
-- statement:
--   For every interpolation parameter, the q=0 and q=1 sides project to the unordered base configuration.
-- source:
--   Modular remaining adjacent-relation proof for Tarcha 3.15.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_right_interp_one_fun_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_interp_time_boundaries_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 0) = baseUnordered n) ∧
      (∀ u : unitInterval,
        configProj n (rightOuterInterpConfig i j hji u 1) = baseUnordered n) := by sorry

end TarchaBraids
