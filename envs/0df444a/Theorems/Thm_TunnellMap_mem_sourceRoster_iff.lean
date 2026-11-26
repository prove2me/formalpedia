-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceRoster_iff
-- name    : TunnellMap.mem_sourceRoster_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:20:48.170678+00:00
-- url     : https://prove2.me/theorems/5b7b47b8-430e-4210-ab10-7c2f04c0ced0
-- title:
--   Tunnell Map: mem source Roster iff
-- statement:
--   The Tunnell Map construction uses the mem source Roster iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L245-L253
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L245-L253

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap
variable {n : ℤ} [Fintype (BOddRep n)]
open RecordDA

theorem TunnellMap.mem_sourceRoster_iff (x : BResidual n) :
    x ∈ sourceRoster n ↔
      canonicalBResidualRepresentative ((bResidualInvolution n).orbit x) = x := by sorry
