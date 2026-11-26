-- Prove2me | Theorems.Thm_Sabidussi_sum_localDifference_occurrences
-- name    : Sabidussi.sum_localDifference_occurrences
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:28.997004+00:00
-- url     : https://prove2.me/theorems/aa16a7f8-a8b8-5f52-9052-1584a071372b
-- title:
--   Sabidussi: sum local Difference occurrences
-- statement:
--   The Sabidussi construction uses the sum local Difference occurrences property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L57-L68
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LocalPattern.lean#L57-L68

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.sum_localDifference_occurrences (n : ℕ) (c : Fin 3) :
    ∑ i, localDifference n c i = 0 := by sorry
