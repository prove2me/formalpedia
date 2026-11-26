-- Prove2me | Theorems.Thm_Sabidussi_localDifference_one
-- name    : Sabidussi.localDifference_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:49.357662+00:00
-- url     : https://prove2.me/theorems/57128e49-2fd9-5e4b-b42b-b33ddd010689
-- title:
--   Sabidussi: local Difference one
-- statement:
--   The Sabidussi construction uses the local Difference one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L44-L45
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L44-L45

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.localDifference_one (c : Fin 3) :
    localDifference 1 c = tripleDifference (choiceColor c) := by sorry

attribute [defeq] Sabidussi.localDifference_one
