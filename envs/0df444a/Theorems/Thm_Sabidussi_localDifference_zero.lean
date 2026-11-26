-- Prove2me | Theorems.Thm_Sabidussi_localDifference_zero
-- name    : Sabidussi.localDifference_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:47.322173+00:00
-- url     : https://prove2.me/theorems/842d6a45-e868-5d2b-81ba-1503d61e00ae
-- title:
--   Sabidussi: local Difference zero
-- statement:
--   The Sabidussi construction uses the local Difference zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L40-L41
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L40-L41

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.localDifference_zero (c : Fin 3) :
    localDifference 0 c = doubleDifference (choiceColor c) := by sorry

attribute [defeq] Sabidussi.localDifference_zero
