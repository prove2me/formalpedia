-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_influence_eq_readers
-- name    : QEC.Coding.BDL26RXInfluenceBounds.influence_eq_readers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:43:52.864844+00:00
-- url     : https://prove2.me/theorems/f3e80172-32c2-4e1c-afc2-a646e31fb422
-- title:
--   BDL26 RXInfluence Bounds: influence eq readers
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the influence eq readers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L162-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L162-L167

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

theorem QEC.Coding.BDL26RXInfluenceBounds.influence_eq_readers (q : FamilyQ S depth i.succ) :
    influence S depth i h q = (hammingSupport (basisSyndrome S depth i q)).biUnion
      (readers S depth i h) := by sorry
