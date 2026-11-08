-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_exact_relation
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_exact_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:27:13.602083+00:00
-- url     : https://prove2.me/theorems/bb8a634e-1c94-40d4-85b8-bae13e957186
-- title:
--   RZCoarse Graining: rz exact relation
-- statement:
--   The RZCoarse Graining construction uses the rz exact relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L433-L450
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L433-L450

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC
open QEC.Coding
open QEC.Coding.MultiscaleDecoder
open QEC.Coding.MultiscaleDecoder.RZCoarseGraining
open scoped BigOperators
universe u v
variable {depth : Nat}
variable {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)]
  [∀ i, Fintype (C2 i)]
variable [∀ i, DecidableEq (C1 i)] [∀ i, DecidableEq (C2 i)]
variable {D : BDL26DecoderData depth C0 C1 C2}
variable {i : StepIndex depth}
variable {V : Type v} [Fintype V] [DecidableEq V]
open RZCoarseGrainingData

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_exact_relation
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hEven : i.succ.val % 2 = 0)
    (sigma : UpperSyndrome D i) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma.1) +
        (D.selectedMap i).map2 (coarseSyndrome A hcompat sigma) := by sorry
