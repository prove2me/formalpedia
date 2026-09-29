-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_outer_one_endpoint_v1
-- name    : TarchaBraids.thm_3_15_adjacent_outer_one_endpoint_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:33:53.526565+00:00
-- url     : https://prove2.me/theorems/e0f62790-bf02-472c-bfe5-5665796a7d8c
-- title:
--   Tarcha 3.15 outer rotation has the common q=1 endpoint
-- statement:
--   For adjacent strands with the required third local strand, the explicit outer-rotation comparison path ends at the same outer-strand transposition of the ordered base configuration.
-- source:
--   Modular q=1 outer-rotation endpoint extraction from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_outer_one_endpoint_v1 :
    ∀ {n : ℕ} (i j : Fin (n - 1)) (hji : (j : ℕ) = (i : ℕ) + 1)
      (hi2 : (i : ℕ) + 2 < n),
      outerRotateFun n i 1 =
        (baseOrdered n).1 ∘ Equiv.swap (strandIdx i) (strandIdxSucc j) := by sorry

end TarchaBraids
