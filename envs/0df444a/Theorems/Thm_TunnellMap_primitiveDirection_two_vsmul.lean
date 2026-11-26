-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirection_two_vsmul
-- name    : TunnellMap.primitiveDirection_two_vsmul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:56:18.864853+00:00
-- url     : https://prove2.me/theorems/53c2cbbe-d862-4620-99c9-098732db4da2
-- title:
--   Tunnell Map: primitive Direction two vsmul
-- statement:
--   The Tunnell Map construction uses the primitive Direction two vsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L304-L306
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L304-L306

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirection_two_vsmul {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection (vsmul 2 v) = primitiveDirection v := by sorry
