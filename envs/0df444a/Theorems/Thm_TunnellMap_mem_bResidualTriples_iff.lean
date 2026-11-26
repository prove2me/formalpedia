-- Prove2me | Theorems.Thm_TunnellMap_mem_bResidualTriples_iff
-- name    : TunnellMap.mem_bResidualTriples_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:42:16.241799+00:00
-- url     : https://prove2.me/theorems/138ba1e6-9909-422d-8148-9f9e6adebd7d
-- title:
--   Tunnell Map: mem b Residual Triples iff
-- statement:
--   The Tunnell Map construction uses the mem b Residual Triples iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L91-L126
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L91-L126

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_bResidualTriples_iff {n : ℤ} (w : Triple) :
    w ∈ bResidualTriples n ↔ (bForm w = n ∧ Odd w.z) ∧ ¬ SourceUsedTriple w := by sorry
