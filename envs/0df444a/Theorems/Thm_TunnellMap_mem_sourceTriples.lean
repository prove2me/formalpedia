-- Prove2me | Theorems.Thm_TunnellMap_mem_sourceTriples
-- name    : TunnellMap.mem_sourceTriples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:04:48.176809+00:00
-- url     : https://prove2.me/theorems/c457462c-a26e-5ac3-b9cc-516cd324c820
-- title:
--   Tunnell Map: mem source Triples
-- statement:
--   The Tunnell Map construction uses the mem source Triples property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L96-L108
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableRoster.lean#L96-L108

import Definitions.Def_TunnellMap_RecordDeferredAcceptanceCorrect
import Definitions.Def_TunnellMap_CanonicalSignLift
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_KernelArith
import Definitions.Def_TunnellMap_ComputableRoster
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_sourceTriples {n : ℤ} {w : Triple} (h : bForm w = n) :
    w ∈ sourceTriples n := by sorry
