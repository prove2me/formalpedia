-- Prove2me | Theorems.Thm_Sabidussi_cast_colorFiber_card
-- name    : Sabidussi.cast_colorFiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:58.54902+00:00
-- url     : https://prove2.me/theorems/9c4551a4-7a41-47d7-bbfd-7d33f07b0768
-- title:
--   Sabidussi: cast color Fiber card
-- statement:
--   The Sabidussi construction uses the cast color Fiber card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L77-L82
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L77-L82

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.cast_colorFiber_card {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Color) (c : Color) :
    ((colorFiber f c).card : F₂) = ∑ i, if f i = c then 1 else 0 := by sorry
