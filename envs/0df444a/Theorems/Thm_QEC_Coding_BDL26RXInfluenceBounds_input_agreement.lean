-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_input_agreement
-- name    : QEC.Coding.BDL26RXInfluenceBounds.input_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:45:50.605917+00:00
-- url     : https://prove2.me/theorems/9c455207-a37b-42d0-b758-c1ecc57ee82d
-- title:
--   BDL26 RXInfluence Bounds: input agreement
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the input agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L233-L239
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L233-L239

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_GraphQuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXInfluenceBounds
import Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_input_agreement

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXInfluenceBounds
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter BDL26RXCoarseInfluence BDL26BoundedValence
open BDL26GraphQuantitativeBounds BDL26RZMap1CoordinateBridge
open MultiscaleDecoder RXCoarseGraining RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators
variable (S : OddScale) (depth : Nat) (i : StepIndex depth) (h : i.val % 2 = 0)

theorem QEC.Coding.BDL26RXInfluenceBounds.input_agreement (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) :
    sigma.val p = (sigmaPlusError S depth i sigma e).val p := by sorry
