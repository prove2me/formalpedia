-- Prove2me | Theorems.Thm_TunnellMap_sourceRosterExec_eq_sourceRoster
-- name    : TunnellMap.sourceRosterExec_eq_sourceRoster
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:19:54.694307+00:00
-- url     : https://prove2.me/theorems/d22da475-eea7-404a-ba1a-4b8eccd501a5
-- title:
--   Tunnell Map: source Roster Exec eq source Roster
-- statement:
--   **The computable roster is the manuscript's source roster.**
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L276-L283
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L276-L283

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA

theorem TunnellMap.sourceRosterExec_eq_sourceRoster :
    sourceRosterExec n = sourceRoster n := by sorry
