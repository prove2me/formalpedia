-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_basisSyndrome_valid
-- name    : QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_valid
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:41:21.569185+00:00
-- url     : https://prove2.me/theorems/216d67ac-2068-4f7d-84b1-3d379be3e23f
-- title:
--   BDL26 RXCoarse Influence: basis Syndrome valid
-- statement:
--   The BDL26 RXCoarse Influence construction uses the basis Syndrome valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L24-L27
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L24-L27

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.basisSyndrome_valid (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (q : FamilyQ S depth i.succ) :
    basisSyndrome S depth i q ∈ (indexedFamily S depth).syndromeSubmodule i.succ := by sorry
