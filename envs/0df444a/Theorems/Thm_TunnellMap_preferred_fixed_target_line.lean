-- Prove2me | Theorems.Thm_TunnellMap_preferred_fixed_target_line
-- name    : TunnellMap.preferred_fixed_target_line
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:25:47.023836+00:00
-- url     : https://prove2.me/theorems/e8ff67c6-4e38-52fe-abbc-b5e9030187c2
-- title:
--   Tunnell Map: preferred fixed target line
-- statement:
--   The Tunnell Map construction uses the preferred fixed target line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L489-L515
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/ProjectiveKey.lean#L489-L515

import Definitions.Def_TunnellMap_PrimitiveDirection
import Definitions.Def_TunnellMap_GloballyRankedExistence
import Definitions.Def_TunnellMap_ProjectiveKey
set_option autoImplicit true
open TunnellMap

theorem TunnellMap.preferred_fixed_target_line {n : ℤ} (s : BResidual n) (t : AResidual n) :
    ∃ c : ℤ, c ≠ 0 ∧
      (vadd (residualTargetLift t) (residualSourceLift s) =
          vsmul c (primitiveDirection (preferredVector s t)) ∨
       vsub (residualTargetLift t) (residualSourceLift s) =
          vsmul c (primitiveDirection (preferredVector s t))) := by sorry
