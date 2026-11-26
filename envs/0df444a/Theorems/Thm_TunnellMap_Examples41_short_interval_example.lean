-- Prove2me | Theorems.Thm_TunnellMap_Examples41_short_interval_example
-- name    : TunnellMap.Examples41.short_interval_example
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:44:31.885921+00:00
-- url     : https://prove2.me/theorems/e41fab1f-508f-55a4-a160-057e367daaa6
-- title:
--   Examples41: short interval example
-- statement:
--   The Examples41 construction uses the short interval example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L46-L56
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41Generator.lean#L46-L56

import Definitions.Def_TunnellMap_Examples41Residual
import Definitions.Def_TunnellMap_Examples41Generator
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
open OrderedGenerator
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.short_interval_example :
    qForm ⟨1, -4, 1⟩ = 20 ∧
      qBilinear (residualSourceLift s2) ⟨1, -4, 1⟩ = 20 ∧
      M 41 20 1 = 420 ∧
      Int.sqrt 420 = 20 ∧
      bLower 41 frame41 20 1 = -4 ∧
      bUpper 41 frame41 20 1 = -4 ∧
      frame41.halfDiscriminant 20 1 (-4) = 4 := by sorry
