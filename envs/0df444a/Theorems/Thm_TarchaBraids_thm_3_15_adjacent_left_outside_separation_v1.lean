-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_outside_separation_v1
-- name    : TarchaBraids.thm_3_15_adjacent_left_outside_separation_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:50:35.377597+00:00
-- url     : https://prove2.me/theorems/a9fefde7-f723-4423-9a0c-727d2e4db10a
-- title:
--   Tarcha 3.15 left interpolation local-to-outside separation
-- statement:
--   Throughout the explicit left interpolation, each distinguished local strand remains distinct from every nonlocal strand.
-- source:
--   Modular local-to-outside separation layer of the explicit adjacent Artin relation interpolation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_left_outside_separation_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentLeftOutsideSeparationFacts i j hji := by sorry

end TarchaBraids
