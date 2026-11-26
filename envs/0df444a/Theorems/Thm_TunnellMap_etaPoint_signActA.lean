-- Prove2me | Theorems.Thm_TunnellMap_etaPoint_signActA
-- name    : TunnellMap.etaPoint_signActA
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:12:44.161058+00:00
-- url     : https://prove2.me/theorems/62b70fd8-dfeb-5235-a494-d220f1a6d7c5
-- title:
--   Tunnell Map: eta Point sign Act A
-- statement:
--   The Tunnell Map construction uses the eta Point sign Act A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L383-L388
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/CanonicalSignLift.lean#L383-L388

import Definitions.Def_TunnellMap_OrbitLift
import Definitions.Def_TunnellMap_ResidualTargetTest
import Definitions.Def_TunnellMap_ComputableDirection
import Definitions.Def_TunnellMap_CanonicalSignLift
set_option autoImplicit true
open TunnellMap
variable {n : ℤ}

theorem TunnellMap.etaPoint_signActA {n : ℤ} (hnpos : 0 < n) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (s : BResidual n) (t : AResidual n) :
    etaPoint s (signActA hnpos σ t) = σ * etaPoint s t := by sorry
