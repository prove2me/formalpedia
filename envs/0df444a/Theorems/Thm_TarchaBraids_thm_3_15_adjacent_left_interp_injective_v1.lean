-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_interp_injective_v1
-- name    : TarchaBraids.thm_3_15_adjacent_left_interp_injective_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T09:02:20.745994+00:00
-- url     : https://prove2.me/theorems/5d83db49-2330-49b6-8c16-852809f07b87
-- title:
--   Tarcha 3.15 left adjacent interpolation is injective
-- statement:
--   For adjacent strands, every stage of the explicit left homotopy between the three-half-twist word and the outer-rotation comparison path is collision-free on the closed unit square.
-- source:
--   Assembly of the modular pairwise and local-to-outside separation results for Tarcha's adjacent Artin relation.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_left_interp_injective_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (u q : ℝ), 0 ≤ u → u ≤ 1 → 0 ≤ q → q ≤ 1 →
      Function.Injective (leftOuterInterpFun n i j u q) := by sorry

end TarchaBraids
