-- Prove2me | Theorems.Thm_TarchaBraids_standardPureBraidWord_higher_filter_succ_v1
-- name    : TarchaBraids.standardPureBraidWord_higher_filter_succ_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T16:59:14.943213+00:00
-- url     : https://prove2.me/theorems/5854b195-8d78-4ab1-951d-64bfc3abffec
-- title:
--   Higher-index filtration under far-right strand extension
-- statement:
--   The higher-index list for a punctured-plane standard loop on n+2 strands is the mapped higher-index list for n+1 strands followed by the new last index.
-- source:
--   Tarcha Theorem 3.11; finite-list identity supporting algebraic transport of the classical pure-braid generator word.

import Mathlib

namespace TarchaBraids

theorem standardPureBraidWord_higher_filter_succ_v1 (n : ℕ) (j : Fin n) :
    (List.finRange (n + 1)).filter (fun k : Fin (n + 1) => j.castSucc < k) =
      (((List.finRange n).filter (fun k : Fin n => j < k)).map Fin.castSucc) ++
        [Fin.last n] := by sorry

end TarchaBraids
