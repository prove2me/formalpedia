-- Prove2me | Theorems.Thm_TarchaBraids_standardPureBraidWord_list_transport_v1
-- name    : TarchaBraids.standardPureBraidWord_list_transport_v1
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-22T21:42:26.704597+00:00
-- url     : https://prove2.me/theorems/5dca223f-2817-4617-86e8-3f2e72166b37
-- title:
--   Classical pure braid signed-word recurrence under far-right strand extension
-- statement:
--   The classical signed pure braid word for the old index embedded in one extra strand equals the final positive half-twist, the embedded old classical word, and the final negative half-twist. This is the exact combinatorial input for algebraic strand transport.
-- source:
--   Tarcha Theorem 3.11; classical pure braid generator recurrence, using accepted higher-filter child 5854b195-8d78-4ab1-951d-64bfc3abffec.

import Mathlib
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_higher_filter_succ_v1

open TarchaBraids

namespace TarchaBraids

theorem standardPureBraidWord_list_transport_v1 (n : ℕ) (j : Fin n) :
    standardPureBraidWord (n + 1) j.castSucc =
      [{ index := (Fin.last n : Fin (n + 2 - 1)),
         sign := BraidLetterSign.positive }] ++
      (standardPureBraidWord n j).map
        (fun a : BraidLetter (n + 1) =>
          ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
             BraidLetter (n + 2))) ++
      [{ index := (Fin.last n : Fin (n + 2 - 1)),
         sign := BraidLetterSign.negative }] := by sorry

end TarchaBraids
