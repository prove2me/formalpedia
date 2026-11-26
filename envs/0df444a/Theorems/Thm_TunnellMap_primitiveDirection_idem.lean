-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirection_idem
-- name    : TunnellMap.primitiveDirection_idem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:10.547151+00:00
-- url     : https://prove2.me/theorems/0dec6a6f-b4a8-4362-aed3-a804bce078f2
-- title:
--   Tunnell Map: primitive Direction idem
-- statement:
--   The Tunnell Map construction uses the primitive Direction idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L293-L297
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L293-L297

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirection_idem {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (primitiveDirection v) = primitiveDirection v := by sorry
