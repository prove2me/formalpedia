-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_coarse_eq_outside_influence
-- name    : QEC.Coding.BDL26RXCoarseInfluence.coarse_eq_outside_influence
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:17:21.454984+00:00
-- url     : https://prove2.me/theorems/a74b96d7-fa69-4fcb-8207-99301f6277eb
-- title:
--   BDL26 RXCoarse Influence: coarse eq outside influence
-- statement:
--   The BDL26 RXCoarse Influence construction uses the coarse eq outside influence property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L141-L152
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L141-L152

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.coarse_eq_outside_influence (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (_hi : 2 ≤ i.val) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) :
    (rxStepOutput S depth i h sigma).coarse.val z =
      (rxStepOutput S depth i h (sigmaPlus S depth i sigma q)).coarse.val z := by sorry
