-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_AuditedLeafAdapters_rzOutput_coarse
-- name    : QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T14:24:23.499381+00:00
-- url     : https://prove2.me/theorems/53b4b4c1-c285-4b9b-8d7a-3be4b255f2e9
-- title:
--   Audited Leaf Adapters: rz Output coarse
-- statement:
--   The Audited Leaf Adapters construction uses the rz Output coarse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1281-L1297
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/Assembly.lean#L1281-L1297

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

theorem QEC.Coding.MultiscaleDecoder.AuditedLeafAdapters.rzOutput_coarse
    {V : Type v} [Fintype V] [DecidableEq V]
    {i : StepIndex depth}
    (A : RZCoarseGraining.RZCoarseGrainingData D i V)
    (hcoh : RZCoarseGraining.LocalTopCohomologyIdentification A)
    (hcompat : RZCoarseGraining.InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : D.family.Syndrome i.succ) :
    (rzOutput A hcoh hcompat hEven sigma).coarse =
      RZCoarseGraining.coarseSyndrome A hcompat sigma := by sorry
