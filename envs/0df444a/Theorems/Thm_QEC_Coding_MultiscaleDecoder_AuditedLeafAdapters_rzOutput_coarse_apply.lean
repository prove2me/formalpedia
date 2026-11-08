-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedLeafAdapters_rzOutput_coarse_apply
-- name    : QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_coarse_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:27:24.604274+00:00
-- url     : https://prove2.me/theorems/62aad63a-1b0f-4a61-a961-499c36f26394
-- title:
--   Audited Leaf Adapters: rz Output coarse apply
-- statement:
--   The Audited Leaf Adapters construction uses the rz Output coarse apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1299-L1310
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1299-L1310

import Definitions.Def_QEC_Coding_ChainComplex_Duality
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RXCoarseGraining
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Assembly
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open scoped BigOperators
universe u v w x y z
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
open QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters
open RZCoarseGraining RXCoarseGraining
variable {D : BDL26DecoderData depth C0 C1 C2}
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]

theorem QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_coarse_apply
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) (z : C2 i.castSucc) :
    ((rzOutput A hcoh hcompat hEven sigma).coarse : D.family.Cochain2 i.castSucc) z =
      RZCoarseGraining.RZCoarseGrainingData.topParity A sigma.1 z := by sorry
