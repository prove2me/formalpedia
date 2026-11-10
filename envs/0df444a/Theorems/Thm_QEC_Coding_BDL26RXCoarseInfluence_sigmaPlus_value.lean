-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_sigmaPlus_value
-- name    : QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_value
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:41:56.498493+00:00
-- url     : https://prove2.me/theorems/3461a18b-a6eb-43b9-bff0-e4c2d2a7dcf9
-- title:
--   BDL26 RXCoarse Influence: sigma Plus value
-- statement:
--   The BDL26 RXCoarse Influence construction uses the sigma Plus value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L40-L42
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L40-L42

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_value (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    (sigmaPlus S depth i sigma q).val = sigma.val + basisSyndrome S depth i q := by sorry
