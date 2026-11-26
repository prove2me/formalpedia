-- Prove2me | Theorems.Thm_TunnellMap_Examples41_residual_inverse_sign_example
-- name    : TunnellMap.Examples41.residual_inverse_sign_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:23:25.607871+00:00
-- url     : https://prove2.me/theorems/8d89e1d0-4c7d-4f7d-9b33-8c917a591c45
-- title:
--   Examples41: residual inverse sign example
-- statement:
--   The Examples41 construction uses the residual inverse sign example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L198-L203
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Matching.lean#L198-L203

import Definitions.Def_TunnellMap_Examples41Generator
import Definitions.Def_TunnellMap_Sharpness
import Definitions.Def_TunnellMap_Examples41Matching
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open GloballyRanked
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.residual_inverse_sign_example :
    negTriple (residualTargetLift t2) = ⟨4, -3, 0⟩ ∧
      negTriple (negTriple (residualSourceLift s2)) = residualSourceLift s2 ∧
      s2.1.1 = ⟨-2, -5, 1⟩ := by sorry
