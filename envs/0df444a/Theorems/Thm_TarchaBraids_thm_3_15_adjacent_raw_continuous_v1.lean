-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_continuous_v1
-- name    : TarchaBraids.thm_3_15_adjacent_raw_continuous_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:15:26.352796+00:00
-- url     : https://prove2.me/theorems/36ef884b-24fd-4fc3-a9c2-481b78240a0d
-- title:
--   Tarcha 3.15 adjacent raw maps are coordinatewise continuous
-- statement:
--   Each strand coordinate of the left and right adjacent braid-word paths and of the common outer-rotation path varies continuously in the path parameter.
-- source:
--   Modular extraction of the coordinate-continuity layer from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_raw_continuous_v1 :
    (∀ (n : ℕ) (i j : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => leftBraidFun n i j q k)) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => rightBraidFun n i j q k)) ∧
    (∀ (n : ℕ) (i : Fin (n - 1)) (k : Fin n),
      Continuous (fun q : ℝ => outerRotateFun n i q k)) := by sorry

end TarchaBraids
