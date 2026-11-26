-- Prove2me | Theorems.Thm_TunnellMap_tripleLexKey_residualTargetLift_lt_iff
-- name    : TunnellMap.tripleLexKey_residualTargetLift_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:48:37.833856+00:00
-- url     : https://prove2.me/theorems/e421d2c4-3ee3-47b2-9d6e-5e7dab8c20f5
-- title:
--   Tunnell Map: triple Lex Key residual Target Lift lt iff
-- statement:
--   The Tunnell Map construction uses the triple Lex Key residual Target Lift lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L139-L144
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ResidualTargetTest.lean#L139-L144

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.tripleLexKey_residualTargetLift_lt_iff {n : ℤ} (t₁ t₂ : AResidual n) :
    tripleLexKey (residualTargetLift t₁) < tripleLexKey (residualTargetLift t₂) ↔
      aResidualLexKey t₁ < aResidualLexKey t₂ := by sorry
