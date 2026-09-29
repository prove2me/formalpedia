-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_interp_one_fun_v1
-- name    : TarchaBraids.thm_3_15_right_interp_one_fun_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T12:12:52.108634+00:00
-- url     : https://prove2.me/theorems/a0f754c7-5436-4017-be78-b9f85a02ac7a
-- title:
--   Tarcha 3.15 right interpolation q=1 endpoint permutation
-- statement:
--   At q=1 every point of the right interpolation is the same endpoint configuration, namely the base ordered configuration with the two outer local strands swapped.
-- source:
--   Modular remaining adjacent-relation proof for Tarcha 3.15.

import Mathlib
import Definitions.Def_TarchaBraids_right_interp_config_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_interp_one_fun_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (u : unitInterval),
      (rightOuterInterpConfig i j hji u 1).1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by sorry

end TarchaBraids
