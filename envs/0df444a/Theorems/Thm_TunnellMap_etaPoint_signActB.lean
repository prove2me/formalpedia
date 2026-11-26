-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_signActB
-- name    : TunnellMap.etaPoint_signActB
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:12:59.993648+00:00
-- url     : https://prove2.me/theorems/1433dff5-fc9b-4e4c-b8c4-b4492955b232
-- title:
--   Tunnell Map: eta Point sign Act B
-- statement:
--   The Tunnell Map construction uses the eta Point sign Act B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L376-L381
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L376-L381

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_signActB {n : ℤ} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (s : BResidual n) (t : AResidual n) :
    etaPoint (signActB σ s) t = σ * etaPoint s t := by sorry
