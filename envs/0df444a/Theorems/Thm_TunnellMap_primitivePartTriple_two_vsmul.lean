-- Prove2me | Theorems.Thm_TunnellMap_primitivePartTriple_two_vsmul
-- name    : TunnellMap.primitivePartTriple_two_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:46.561004+00:00
-- url     : https://prove2.me/theorems/718170fe-0483-4866-b680-f298070116c0
-- title:
--   Tunnell Map: primitive Part Triple two vsmul
-- statement:
--   The Tunnell Map construction uses the primitive Part Triple two vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L157-L161
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L157-L161

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitivePartTriple_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitivePartTriple (vsmul 2 v) = primitivePartTriple v := by sorry
