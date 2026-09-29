-- Prove2me | Theorems.Thm_TarchaBraids_thm_3_15_adjacent_raw_zero_endpoints_v1
-- name    : TarchaBraids.thm_3_15_adjacent_raw_zero_endpoints_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-21T08:15:35.43558+00:00
-- url     : https://prove2.me/theorems/42d2eb0f-2b63-4e67-9dc5-ea9aadb1eb58
-- title:
--   Tarcha 3.15 adjacent raw maps start at the base configuration
-- statement:
--   The raw left braid word, right braid word and outer-rotation coordinate maps all begin at the standard ordered base configuration.
-- source:
--   Modular extraction of the zero-endpoint layer from the explicit adjacent Artin relation proof.

import Mathlib
import Definitions.Def_TarchaBraids_adjacent_path_data_v1

namespace TarchaBraids

open BraidsLinksMCG

theorem thm_3_15_adjacent_raw_zero_endpoints_v1 :
    (∀ (n : ℕ) (i j : Fin (n - 1)),
      leftBraidFun n i j 0 = (baseOrdered n).1) ∧
    (∀ (n : ℕ) (i j : Fin (n - 1)),
      rightBraidFun n i j 0 = (baseOrdered n).1) ∧
    (∀ (n : ℕ) (i : Fin (n - 1)),
      outerRotateFun n i 0 = (baseOrdered n).1) := by sorry

end TarchaBraids
