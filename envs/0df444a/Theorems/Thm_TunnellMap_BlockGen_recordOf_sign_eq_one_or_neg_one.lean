-- Prove2me | Theorems.Thm_TunnellMap_BlockGen_recordOf_sign_eq_one_or_neg_one
-- name    : TunnellMap.BlockGen.recordOf_sign_eq_one_or_neg_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:32:19.848527+00:00
-- url     : https://prove2.me/theorems/146ddbae-6f84-4613-933d-fa69d277d7ca
-- title:
--   Block Gen: record Of sign eq one or neg one
-- statement:
--   The Block Gen construction uses the record Of sign eq one or neg one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L449-L452
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/BlockGeneratorCorrect.lean#L449-L452

import Definitions.Def_TunnellMap_BlockGenerator
import Definitions.Def_TunnellMap_BlockGeneratorCorrect
set_option autoImplicit true
open TunnellMap
open TunnellMap.BlockGen
open OrderedGenerator
variable {n : ℤ} {p : Triple}
variable {s : BResidual n}

theorem TunnellMap.BlockGen.recordOf_sign_eq_one_or_neg_one
    (F : OrthogonalFrame (tau (residualSourceLift s))) (i : GeneratorIndex) :
    (recordOf s F i).sign = 1 ∨ (recordOf s F i).sign = -1 := by sorry
