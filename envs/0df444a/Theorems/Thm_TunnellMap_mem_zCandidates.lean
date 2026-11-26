-- Prove2me | Theorems.Thm_TunnellMap_mem_zCandidates
-- name    : TunnellMap.mem_zCandidates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:17:53.284865+00:00
-- url     : https://prove2.me/theorems/e5809742-0566-5fa7-b7e6-4a5923514c50
-- title:
--   Tunnell Map: mem z Candidates
-- statement:
--   The Tunnell Map construction uses the mem z Candidates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L69-L88
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L69-L88

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_zCandidates {r z : ℤ} (h : 8 * (z * z) = r) : z ∈ zCandidates r := by sorry
