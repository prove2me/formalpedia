-- Prove2me | Theorems.Thm_TunnellMap_tau_injective
-- name    : TunnellMap.tau_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:33.373372+00:00
-- url     : https://prove2.me/theorems/02422c7d-7d27-41ca-8ca3-c14b4bec92df
-- title:
--   Tunnell Map: tau injective
-- statement:
--   The Tunnell Map construction uses the tau injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/TauLattice.lean#L65-L67
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/TauLattice.lean#L65-L67

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_TauLattice
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.tau_injective : Function.Injective tau := by sorry
