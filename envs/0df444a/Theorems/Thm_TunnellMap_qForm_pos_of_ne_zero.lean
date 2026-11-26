-- Prove2me | Theorems.Thm_TunnellMap_qForm_pos_of_ne_zero
-- name    : TunnellMap.qForm_pos_of_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:22:55.013361+00:00
-- url     : https://prove2.me/theorems/921cbb4d-8f71-4d5f-af4f-b6d01c61c70e
-- title:
--   Tunnell Map: q Form pos of ne zero
-- statement:
--   The Tunnell Map construction uses the q Form pos of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L30-L48
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L30-L48

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.qForm_pos_of_ne_zero {p : Triple} (hp : p ≠ ⟨0, 0, 0⟩) : 0 < qForm p := by sorry
