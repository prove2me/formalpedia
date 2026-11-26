-- Prove2me | Theorems.Thm_Sabidussi_quadratic_sum_fin
-- name    : Sabidussi.quadratic_sum_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:25.352142+00:00
-- url     : https://prove2.me/theorems/7491ecb5-76bf-55ea-819b-4aa5c678ea6c
-- title:
--   Sabidussi: quadratic sum fin
-- statement:
--   Polarization of `quadratic` along a finite linearly ordered word.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L63-L70
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L63-L70

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.quadratic_sum_fin : ∀ {n : ℕ} (f : Fin n → Color),
    quadratic (∑ i, f i) = (∑ i, quadratic (f i)) + orderedPairBracket f
  := by sorry
