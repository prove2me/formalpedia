-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_word_one_endpoints_v1
-- name    : TarchaBraids.thm_3_15_adjacent_word_one_endpoints_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:33:28.206689+00:00
-- url     : https://prove2.me/theorems/1f92af3c-c99e-4f90-8a50-6648c34d8aa9
-- title:
--   Tarcha 3.15 adjacent braid words have the common q=1 endpoint
-- statement:
--   For adjacent strands, both explicit three-half-twist coordinate words end at the same ordered configuration, obtained from the base configuration by swapping the two outer local strands.
-- source:
--   Modular q=1 endpoint extraction from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_word_one_endpoints_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)), (j : ℕ) = (i : ℕ) + 1 →
      leftBraidFun n i j 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) ∧
      rightBraidFun n i j 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by sorry

end TarchaBraids
