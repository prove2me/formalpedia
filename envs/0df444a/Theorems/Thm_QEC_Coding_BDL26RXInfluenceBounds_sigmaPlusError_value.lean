-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_sigmaPlusError_value
-- name    : QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:45:30.811422+00:00
-- url     : https://prove2.me/theorems/f33c3943-c5d0-42fc-b1b4-efa0285fdba1
-- title:
--   BDL26 RXInfluence Bounds: sigma Plus Error value
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the sigma Plus Error value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L228-L231
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L228-L231

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

theorem QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_value (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) :
    (sigmaPlusError S depth i sigma e).val =
      sigma.val + (indexedFamily S depth).coboundary1 i.succ e := by sorry
