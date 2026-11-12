-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_errorInfluence_basis
-- name    : QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T09:54:53.54797+00:00
-- url     : https://prove2.me/theorems/900a8013-3e23-4b87-aa29-c1480b1467e8
-- title:
--   BDL26 RXInfluence Bounds: error Influence basis
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the error Influence basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L306-L312
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L306-L312

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

theorem QEC.Coding.BDL26RXInfluenceBounds.errorInfluence_basis (q : FamilyQ S depth i.succ) :
    errorInfluence S depth i h (canonicalBasisWord (F := BDL26Field) q) =
      influence S depth i h q := by sorry
