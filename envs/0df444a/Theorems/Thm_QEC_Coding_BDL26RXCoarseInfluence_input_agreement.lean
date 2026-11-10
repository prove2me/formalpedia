-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_input_agreement
-- name    : QEC.Coding.BDL26RXCoarseInfluence.input_agreement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:06:26.941628+00:00
-- url     : https://prove2.me/theorems/fd664966-5394-4c31-95ea-b94d8cae8586
-- title:
--   BDL26 RXCoarse Influence: input agreement
-- statement:
--   The BDL26 RXCoarse Influence construction uses the input agreement property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L103-L109
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L103-L109

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.input_agreement (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (h : i.val % 2 = 0) (sigma : (indexedFamily S depth).Syndrome i.succ)
    (q : FamilyQ S depth i.succ) (z : FamilyZ S depth i.castSucc)
    (hz : z ∉ influence S depth i h q) (p : FamilyZ S depth i.succ)
    (hp : p ∈ readRegion S depth i h z) : sigma.val p = (sigmaPlus S depth i sigma q).val p := by sorry
