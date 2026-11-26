-- Prove2me | Theorems.Thm_Sabidussi_choiceColor_ne_zero
-- name    : Sabidussi.choiceColor_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:58.942383+00:00
-- url     : https://prove2.me/theorems/b6140cae-3c35-5371-84cc-493ccacb111e
-- title:
--   Sabidussi: choice Color ne zero
-- statement:
--   The Sabidussi construction uses the choice Color ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L18-L20
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L18-L20

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.choiceColor_ne_zero (c : Fin 3) : choiceColor c ≠ 0 := by sorry
