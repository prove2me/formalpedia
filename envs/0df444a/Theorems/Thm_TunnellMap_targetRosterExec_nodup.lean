-- Prove2me | Theorems.Thm_TunnellMap_targetRosterExec_nodup
-- name    : TunnellMap.targetRosterExec_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:26:50.693913+00:00
-- url     : https://prove2.me/theorems/91663134-d30b-5f6e-a678-75d87b1ab265
-- title:
--   Tunnell Map: target Roster Exec nodup
-- statement:
--   The Tunnell Map construction uses the target Roster Exec nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L145-L146
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L145-L146

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.targetRosterExec_nodup {n : ℤ} : (targetRosterExec n).Nodup := by sorry
