-- Prove2me | Theorems.Thm_TunnellMap_sourceRosterExec_nodup
-- name    : TunnellMap.sourceRosterExec_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:07:01.16387+00:00
-- url     : https://prove2.me/theorems/071a0fe1-58c8-483e-83fa-7d726a66e792
-- title:
--   Tunnell Map: source Roster Exec nodup
-- statement:
--   The Tunnell Map construction uses the source Roster Exec nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L180-L181
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L180-L181

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.sourceRosterExec_nodup {n : ℤ} : (sourceRosterExec n).Nodup := by sorry
