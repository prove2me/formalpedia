-- Prove2me | Theorems.Thm_Sabidussi_localDifference_ne_zero
-- name    : Sabidussi.localDifference_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:09:08.033302+00:00
-- url     : https://prove2.me/theorems/0e2586ef-435e-4315-bb6d-f4f242f9fb1e
-- title:
--   Sabidussi: local Difference ne zero
-- statement:
--   The Sabidussi construction uses the local Difference ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L47-L55
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L47-L55

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.localDifference_ne_zero (n : ℕ) (c : Fin 3) (i : Fin (n + 2)) :
    localDifference n c i ≠ 0 := by sorry
