-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_input_difference
-- name    : QEC.Coding.BDL26RXCoarseInfluence.input_difference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T05:42:10.709677+00:00
-- url     : https://prove2.me/theorems/d24cf265-ded6-4276-a078-2dddfa036fe9
-- title:
--   BDL26 RXCoarse Influence: input difference
-- statement:
--   The BDL26 RXCoarse Influence construction uses the input difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L44-L49
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L44-L49

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.input_difference (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    sigma.val + (sigmaPlus S depth i sigma q).val = basisSyndrome S depth i q := by sorry
