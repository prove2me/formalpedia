-- Prove2me | Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
-- name    : P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:44.221881+00:00
-- url     : https://prove2.me/theorems/38508c0a-54b9-4200-871b-3aa0fa0e4a43
-- title:
--   P2 M Tunnell Map dot lin Comb3 cross z e  4b2fa73c6dcf: P2 M Tunnell Map dot lin Comb3 cross z e  4b2fa73c6dcf
-- statement:
--   The P2 M Tunnell Map dot lin Comb3 cross z e  4b2fa73c6dcf construction uses the P2 M Tunnell Map dot lin Comb3 cross z e  4b2fa73c6dcf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L68-L71
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L68-L71

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross z e₁) = b * det3 e₁ e₂ z := by sorry

alias «TunnellMap».«dot_linComb3_cross_z_e₁» := P2M_TunnellMap_dot_linComb3_cross_z_e__4b2fa73c6dcf
