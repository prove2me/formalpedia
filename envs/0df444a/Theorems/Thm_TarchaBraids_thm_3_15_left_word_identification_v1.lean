-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_left_word_identification_v1
-- name    : TarchaBraids.thm_3_15_left_word_identification_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T09:37:37.506903+00:00
-- url     : https://prove2.me/theorems/df92f0a0-71a2-49a4-8f88-e894aac5b90f
-- title:
--   Tarcha 3.15 left piecewise braid path equals the three-half-twist word
-- statement:
--   The projected piecewise left adjacent braid path is exactly the concatenation of the three half-twist loops i, j, i.
-- source:
--   Modular path-identification layer extracted from Tarcha's adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_left_word_identification_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (q : unitInterval),
      configProj n (leftBraidConfig n i j (q : ℝ)) = leftBraidWordLoop n i j q := by sorry

end TarchaBraids
