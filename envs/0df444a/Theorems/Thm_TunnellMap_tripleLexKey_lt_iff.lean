-- Prove2me | Theorems.Thm_TunnellMap_tripleLexKey_lt_iff
-- name    : TunnellMap.tripleLexKey_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:16.412586+00:00
-- url     : https://prove2.me/theorems/32946e4b-7de6-5ee6-ae60-574b32ec55ea
-- title:
--   Tunnell Map: triple Lex Key lt iff
-- statement:
--   The Tunnell Map construction uses the triple Lex Key lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L127-L131
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L127-L131

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.tripleLexKey_lt_iff (u w : Triple) :
    tripleLexKey u < tripleLexKey w ↔
      u.x < w.x ∨ (u.x = w.x ∧ (u.y < w.y ∨ (u.y = w.y ∧ u.z < w.z))) := by sorry
