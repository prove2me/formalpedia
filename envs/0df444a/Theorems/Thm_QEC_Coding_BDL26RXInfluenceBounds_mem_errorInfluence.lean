-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_mem_errorInfluence
-- name    : QEC.Coding.BDL26RXInfluenceBounds.mem_errorInfluence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:44:25.419255+00:00
-- url     : https://prove2.me/theorems/a11f3edf-afa9-48fc-a79d-10de3fe90d28
-- title:
--   BDL26 RXInfluence Bounds: mem error Influence
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the mem error Influence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L182-L186
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L182-L186

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

theorem QEC.Coding.BDL26RXInfluenceBounds.mem_errorInfluence (e : (indexedFamily S depth).Cochain1 i.succ)
    (z : FamilyZ S depth i.castSucc) :
    z ∈ errorInfluence S depth i h e ↔ ∃ q, e q ≠ 0 ∧ z ∈ influence S depth i h q := by sorry
