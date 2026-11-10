-- Prove2me | Theorems.Thm_QEC_Coding_BDL26RXCoarseInfluence_sigmaPlus_preimage
-- name    : QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_preimage
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-10T05:42:13.080749+00:00
-- url     : https://prove2.me/theorems/c05a0d0d-e8d1-4da2-8bed-5ad8fef86ed8
-- title:
--   BDL26 RXCoarse Influence: sigma Plus preimage
-- statement:
--   The BDL26 RXCoarse Influence construction uses the sigma Plus preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L51-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/RXCoarseInfluence.lean#L51-L61

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXCoarseInfluence
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXCoarseInfluence
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26RXDecoderAdapter MultiscaleDecoder RXCoarseGraining
open RXCoarseGraining.RXCoarseGrainingData
open scoped Classical BigOperators

theorem QEC.Coding.BDL26RXCoarseInfluence.sigmaPlus_preimage (S : OddScale) (depth : Nat) (i : StepIndex depth)
    (sigma : (indexedFamily S depth).Syndrome i.succ) (q : FamilyQ S depth i.succ) :
    ∃ e : (indexedFamily S depth).Cochain1 i.succ,
      (indexedFamily S depth).coboundary1 i.succ e = sigma.val ∧
      (indexedFamily S depth).coboundary1 i.succ (e + canonicalBasisWord q) =
        (sigmaPlus S depth i sigma q).val := by sorry
