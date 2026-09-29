-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_injective_v1
-- name    : TarchaBraids.thm_3_15_adjacent_raw_injective_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:15:25.80411+00:00
-- url     : https://prove2.me/theorems/8744bd79-8f29-4e41-af05-0318a6946bfa
-- title:
--   Tarcha 3.15 adjacent raw maps are injective
-- statement:
--   The raw ordered-coordinate maps for the two adjacent three-half-twist words and their common outer-rotation comparison path are injective at every time for which the three local strands exist.
-- source:
--   Modular extraction of the collision-freeness layer from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_raw_injective_v1 :
    (∀ {n : ℕ} (i j : Fin (n - 1)) (q : ℝ),
      Function.Injective (leftBraidFun n i j q)) ∧
    (∀ {n : ℕ} (i j : Fin (n - 1)) (q : ℝ),
      Function.Injective (rightBraidFun n i j q)) ∧
    (∀ {n : ℕ} (i : Fin (n - 1)) (q : ℝ),
      (i : ℕ) + 2 < n → Function.Injective (outerRotateFun n i q)) := by sorry

end TarchaBraids
