-- Prove2me | Theorems.Thm_TunnellMap_sourceRoster_nodup
-- name    : TunnellMap.sourceRoster_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:19:26.626398+00:00
-- url     : https://prove2.me/theorems/11c3a4c9-662a-5b54-939e-a6a1bb8a468d
-- title:
--   Tunnell Map: source Roster nodup
-- statement:
--   The Tunnell Map construction uses the source Roster nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L255-L260
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L255-L260

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA

theorem TunnellMap.sourceRoster_nodup : (sourceRoster n).Nodup := by sorry
