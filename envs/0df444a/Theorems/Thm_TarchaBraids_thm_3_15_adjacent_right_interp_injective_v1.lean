-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_interp_injective_v1
-- name    : TarchaBraids.thm_3_15_adjacent_right_interp_injective_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T11:03:46.597518+00:00
-- url     : https://prove2.me/theorems/e225219e-e0a8-4b88-9d95-7f5f6a88a543
-- title:
--   Tarcha 3.15 right interpolation injectivity
-- statement:
--   For interpolation and path parameters in the unit interval, the right interpolation map is injective on strand indices.
-- source:
--   Case split assembled from modular right pairwise and right distinguished-to-outside separation theorems.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_outside_facts_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_pairwise_separation_v1
import Theorems.Thm_TarchaBraids_thm_3_15_adjacent_right_outside_separation_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_right_interp_injective_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
      Function.Injective (rightOuterInterpFun n i j u q) := by sorry

end TarchaBraids
