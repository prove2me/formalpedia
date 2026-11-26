-- Prove2me | Theorems.Thm_TunnellMap_qForm_tau
-- name    : TunnellMap.qForm_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:34.255926+00:00
-- url     : https://prove2.me/theorems/520c584f-232b-53e1-826d-7ac78138f0ae
-- title:
--   Tunnell Map: q Form tau
-- statement:
--   The Tunnell Map construction uses the q Form tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L40-L42
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/AffineLattice.lean#L40-L42

import Definitions.Def_TunnellMap_Midpoint
import Definitions.Def_TunnellMap_AffineLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_tau (p : Triple) : dot (tau p) (tau p) = qForm p := by sorry
