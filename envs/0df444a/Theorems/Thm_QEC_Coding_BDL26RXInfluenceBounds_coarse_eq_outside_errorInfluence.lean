-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXInfluenceBounds_coarse_eq_outside_errorInfluence
-- name    : QEC.Coding.BDL26RXInfluenceBounds.coarse_eq_outside_errorInfluence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T07:46:39.992244+00:00
-- url     : https://prove2.me/theorems/e319796c-8582-4040-8f74-06808fcfa7b5
-- title:
--   BDL26 RXInfluence Bounds: coarse eq outside error Influence
-- statement:
--   The BDL26 RXInfluence Bounds construction uses the coarse eq outside error Influence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L260-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXInfluenceBounds.lean#L260-L271

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

theorem QEC.Coding.BDL26RXInfluenceBounds.coarse_eq_outside_errorInfluence (hi : 2 ≤ i.val)
    (sigma : (indexedFamily S depth).Syndrome i.succ)
    (e : (indexedFamily S depth).Cochain1 i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ errorInfluence S depth i h e) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlusError S depth i sigma e)).coarse.val z := by sorry
