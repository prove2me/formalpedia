-- Prove2me | Theorems.Thm_TunnellMap_cramer_identity
-- name    : TunnellMap.cramer_identity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:45:21.091697+00:00
-- url     : https://prove2.me/theorems/d5614481-5917-4e5f-ad93-c432277a06b1
-- title:
--   Tunnell Map: cramer identity
-- statement:
--   The Tunnell Map construction uses the cramer identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L57-L61
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L57-L61

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.cramer_identity (r e₁ e₂ z : Triple) :
    linComb3 (dot r (cross e₂ z)) (dot r (cross z e₁))
      (dot r (cross e₁ e₂)) e₁ e₂ z =
      vsmul (det3 e₁ e₂ z) r := by sorry
