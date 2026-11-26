-- Prove2me | Theorems.Thm_Sabidussi_colorFiber_card_even_of_moments
-- name    : Sabidussi.colorFiber_card_even_of_moments
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:08:58.96299+00:00
-- url     : https://prove2.me/theorems/d520ad4e-42d2-41d9-a006-5c8cf464b816
-- title:
--   Sabidussi: color Fiber card even of moments
-- statement:
--   In an even finite family of four colours, vanishing of the two linear moments and of the
--   quadratic moment is equivalent to every colour occurring evenly.  This is the forward direction
--   needed in the Sabidussi argument.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L112-L134
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Parity.lean#L112-L134

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.colorFiber_card_even_of_moments {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Color) (hcard : Even (Fintype.card I))
    (hsum : ∑ i, f i = 0) (hquadratic : ∑ i, quadratic (f i) = 0) (c : Color) :
    Even (colorFiber f c).card := by sorry
