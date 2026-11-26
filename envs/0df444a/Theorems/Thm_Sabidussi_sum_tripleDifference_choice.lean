-- Prove2me | Theorems.Thm_Sabidussi_sum_tripleDifference_choice
-- name    : Sabidussi.sum_tripleDifference_choice
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:10.957322+00:00
-- url     : https://prove2.me/theorems/2119f3c4-01e3-437e-bbc0-9ae4e4965bc1
-- title:
--   Sabidussi: sum triple Difference choice
-- statement:
--   The Sabidussi construction uses the sum triple Difference choice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L25-L28
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L25-L28

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_tripleDifference_choice (i : Fin 3) :
    ∑ c, tripleDifference (choiceColor c) i = 0 := by sorry
