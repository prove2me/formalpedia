-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_sigmaPlusError_basis
-- name    : QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_basis
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T09:49:29.119254+00:00
-- url     : https://prove2.me/theorems/3fd57e12-c97a-4cd8-bcbb-dc27caec47f7
-- title:
--   BDL26 RXInfluence Bounds: sigma Plus Error basis
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the sigma Plus Error basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L314-L317
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L314-L317

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

theorem QEC.Coding.BDL26RXInfluenceBounds.sigmaPlusError_basis (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) :
    sigmaPlusError S depth i sigma (canonicalBasisWord (F := BDL26Field) q) =
      sigmaPlus S depth i sigma q := by sorry
