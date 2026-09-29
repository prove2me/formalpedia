-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_right_word_identification_v1
-- name    : TarchaBraids.thm_3_15_right_word_identification_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T09:37:35.790124+00:00
-- url     : https://prove2.me/theorems/82afdb5e-c647-46af-94aa-5fca1fadc5c3
-- title:
--   Tarcha 3.15 right piecewise braid path equals the three-half-twist word
-- statement:
--   The projected piecewise right adjacent braid path is exactly the concatenation of the three half-twist loops j, i, j.
-- source:
--   Modular path-identification layer extracted from Tarcha's adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_config_data_v1
import Definitions.Def_TarchaBraids_adjacent_word_loops_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_right_word_identification_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (q : unitInterval),
      configProj n (rightBraidConfig n i j (q : ℝ)) = rightBraidWordLoop n i j q := by sorry

end TarchaBraids
