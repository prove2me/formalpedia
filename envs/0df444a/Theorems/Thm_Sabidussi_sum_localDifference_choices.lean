-- Prove2me | Theorems.Thm_Sabidussi_sum_localDifference_choices
-- name    : Sabidussi.sum_localDifference_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:05.776732+00:00
-- url     : https://prove2.me/theorems/09dd270c-802a-5751-bf4a-905abb395509
-- title:
--   Sabidussi: sum local Difference choices
-- statement:
--   The Sabidussi construction uses the sum local Difference choices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L70-L78
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L70-L78

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_localDifference_choices (n : ℕ) (i : Fin (n + 2)) :
    ∑ c, localDifference n c i = 0 := by sorry
