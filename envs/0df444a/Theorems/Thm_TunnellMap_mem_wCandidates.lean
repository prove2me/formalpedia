-- Prove2me | Theorems.Thm_TunnellMap_mem_wCandidates
-- name    : TunnellMap.mem_wCandidates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:27:23.471033+00:00
-- url     : https://prove2.me/theorems/6757f6a5-cd2b-4909-906e-03a22043be5e
-- title:
--   Tunnell Map: mem w Candidates
-- statement:
--   The Tunnell Map construction uses the mem w Candidates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L35-L54
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableTargetRoster.lean#L35-L54

import Definitions.Def_TunnellMap_ComputableRoster
import Definitions.Def_TunnellMap_ComputableTargetRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_wCandidates {r z : ℤ} (h : 32 * (z * z) = r) : z ∈ wCandidates r := by sorry
