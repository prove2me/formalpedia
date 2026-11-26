-- Prove2me | Theorems.Thm_P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb
-- name    : P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:36.421671+00:00
-- url     : https://prove2.me/theorems/fb43d019-94d6-52a0-82b5-4fbf862e9afb
-- title:
--   P2 M Tunnell Map dot lin Comb3 cross e  e  a0a5a8b7bacb: P2 M Tunnell Map dot lin Comb3 cross e  e  a0a5a8b7bacb
-- statement:
--   The P2 M Tunnell Map dot lin Comb3 cross e  e  a0a5a8b7bacb construction uses the P2 M Tunnell Map dot lin Comb3 cross e  e  a0a5a8b7bacb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L73-L76
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L73-L76

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb (a b c : ℤ) (e₁ e₂ z : Triple) :
    dot (linComb3 a b c e₁ e₂ z) (cross e₁ e₂) = c * det3 e₁ e₂ z := by sorry

alias «TunnellMap».«dot_linComb3_cross_e₁_e₂» := P2M_TunnellMap_dot_linComb3_cross_e__e__a0a5a8b7bacb
