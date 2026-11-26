-- Prove2me | Theorems.Thm_TunnellMap_tripleLexLtExec_iff
-- name    : TunnellMap.tripleLexLtExec_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:45:17.349306+00:00
-- url     : https://prove2.me/theorems/dae63555-cc22-579c-9332-c47a22145680
-- title:
--   Tunnell Map: triple Lex Lt Exec iff
-- statement:
--   The Tunnell Map construction uses the triple Lex Lt Exec iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L133-L137
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L133-L137

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.tripleLexLtExec_iff (u w : Triple) :
    tripleLexLtExec u w = true ↔ tripleLexKey u < tripleLexKey w := by sorry
