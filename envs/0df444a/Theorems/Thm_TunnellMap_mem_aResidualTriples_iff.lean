-- Prove2me | Theorems.Thm_TunnellMap_mem_aResidualTriples_iff
-- name    : TunnellMap.mem_aResidualTriples_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T16:42:36.934639+00:00
-- url     : https://prove2.me/theorems/644d790d-3827-53c4-844e-6d70f1469e69
-- title:
--   Tunnell Map: mem a Residual Triples iff
-- statement:
--   The Tunnell Map construction uses the mem a Residual Triples iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L128-L160
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ComputableCounting.lean#L128-L160

import Definitions.Def_TunnellMap_ComputableTargetRoster
import Definitions.Def_TunnellMap_ComputableCounting
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.mem_aResidualTriples_iff {n : ℤ} (w : Triple) :
    w ∈ aResidualTriples n ↔ aForm w = n ∧ ¬ ImageUsedTriple w := by sorry
