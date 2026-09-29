-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_left_pairwise_separation_v1
-- name    : TarchaBraids.thm_3_15_adjacent_left_pairwise_separation_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:50:19.77039+00:00
-- url     : https://prove2.me/theorems/abfe5f64-5ef3-4911-859d-c55aa14bec9e
-- title:
--   Tarcha 3.15 left interpolation pairwise local separation
-- statement:
--   Throughout the explicit left interpolation, the three distinguished local strands remain pairwise distinct for all interpolation and path parameters in the unit interval.
-- source:
--   Modular pairwise-separation layer of the explicit adjacent Artin relation interpolation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_separation_interfaces_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_left_pairwise_separation_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1),
      AdjacentLeftPairwiseSeparationFacts i j hji := by sorry

end TarchaBraids
