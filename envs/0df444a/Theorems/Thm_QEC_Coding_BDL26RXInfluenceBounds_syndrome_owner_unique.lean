-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_syndrome_owner_unique
-- name    : QEC.Coding.BDL26RXInfluenceBounds.syndrome_owner_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:45:34.962208+00:00
-- url     : https://prove2.me/theorems/732103d7-4d8f-4ed7-93b1-91bc8a9f8c63
-- title:
--   BDL26 RXInfluence Bounds: syndrome owner unique
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the syndrome owner unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L119-L123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L119-L123

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

theorem QEC.Coding.BDL26RXInfluenceBounds.syndrome_owner_unique (p : FamilyZ S depth i.succ) :
    ∃! v, p ∈ (rxXiLocalComplex (rxData S depth i h)).syndromeRegion v := by sorry
