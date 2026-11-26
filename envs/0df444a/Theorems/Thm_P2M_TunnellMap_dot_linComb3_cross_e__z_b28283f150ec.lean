-- Prove2me | Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec
-- name    : P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:28.470794+00:00
-- url     : https://prove2.me/theorems/db6fbaab-6654-578a-bee3-429f302f39c3
-- title:
--   P2 M Tunnell Map dot lin Comb3 cross e  z b28283f150ec: P2 M Tunnell Map dot lin Comb3 cross e  z b28283f150ec
-- statement:
--   The P2 M Tunnell Map dot lin Comb3 cross e  z b28283f150ec construction uses the P2 M Tunnell Map dot lin Comb3 cross e  z b28283f150ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L63-L66
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L63-L66

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross e₂ z) = a * det3 e₁ e₂ z := by sorry

alias «TunnellMap».«dot_linComb3_cross_e₂_z» := P2M_TunnellMap_dot_linComb3_cross_e__z_b28283f150ec
