-- Prove2me | Theorems.Thm_TunnellMap_Examples41_midpoint_example
-- name    : TunnellMap.Examples41.midpoint_example
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T16:54:31.462027+00:00
-- url     : https://prove2.me/theorems/0ca2d88c-fe08-4f69-adee-e432ff205bbb
-- title:
--   Examples41: midpoint example
-- statement:
--   The Examples41 construction uses the midpoint example property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L184-L195
-- source:
--   https://github.com/GrgAakash/tunnell-two-to-one-map/blob/d888a7c73c0ef1695dab8c48ccde629fbebb2d46/TunnellMap/Examples41.lean#L184-L195

import Definitions.Def_TunnellMap_ControlCost
import Definitions.Def_TunnellMap_Finiteness
import Definitions.Def_TunnellMap_PureCoordinates
import Definitions.Def_TunnellMap_ResidualDeferredAcceptance
import Definitions.Def_TunnellMap_Examples41
set_option autoImplicit true
open TunnellMap
open TunnellMap.Examples41
set_option maxRecDepth 10000

theorem TunnellMap.Examples41.midpoint_example :
    bLift midpointSource = ⟨-2, -5, 2⟩ ∧
      aLift midpointTarget = ⟨4, -3, 0⟩ ∧
      IsHalfSum ⟨1, -4, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      IsHalfDiff ⟨-3, -1, 1⟩ (bLift midpointSource) (aLift midpointTarget) ∧
      qForm ⟨1, -4, 1⟩ = 20 ∧
      qForm ⟨3, 1, -1⟩ = 21 ∧
      qBilinear ⟨-2, -5, 2⟩ ⟨1, -4, 1⟩ = 20 ∧
      vadd (negTriple ⟨-2, -5, 2⟩) (vsmul 2 ⟨1, -4, 1⟩) =
        ⟨4, -3, 0⟩ := by sorry
