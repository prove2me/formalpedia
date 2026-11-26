-- Prove2me | Theorems.Thm_TunnellMap_primitiveDirection_ne_zero
-- name    : TunnellMap.primitiveDirection_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:14.755137+00:00
-- url     : https://prove2.me/theorems/4136721a-cfd9-4062-8369-34fd0b1bdaa0
-- title:
--   Tunnell Map: primitive Direction ne zero
-- statement:
--   The Tunnell Map construction uses the primitive Direction ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L322-L328
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/PrimitiveDirection.lean#L322-L328

import Definitions.Def_TunnellMap_AffineLattice
import Definitions.Def_TunnellMap_Antipodal
import Definitions.Def_TunnellMap_PrimitiveDirection
set_option autoImplicit true
open TunnellMap
open Polynomial

theorem TunnellMap.primitiveDirection_ne_zero {v : Triple} (hv : v ≠ ⟨0, 0, 0⟩) :
    primitiveDirection v ≠ ⟨0, 0, 0⟩ := by sorry
