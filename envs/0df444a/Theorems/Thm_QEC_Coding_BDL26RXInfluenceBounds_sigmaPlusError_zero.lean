-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_sigmaPlusError_zero
-- name    : QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T06:18:37.251841+00:00
-- url     : https://prove2.me/theorems/58c790d6-cb1c-4413-a0b4-cadfe7c75481
-- title:
--   BDL26 RXInfluence Bounds: sigma Plus Error zero
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the sigma Plus Error zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L301-L304
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L301-L304

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_zero (sigma : (indexedFamily S depth).Syndrome i.succ) :
    sigmaPlusError S depth i sigma 0 = sigma := by sorry
