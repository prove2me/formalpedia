-- Prove2me | Theorems.Thm_QEC_Coding_MultiscaleDecoder_RZCoarseGraining_rz_exact_relation_selected
-- name    : QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_exact_relation_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T13:29:22.314929+00:00
-- url     : https://prove2.me/theorems/328ab5b9-f1c2-4aeb-be18-18519a875db1
-- title:
--   RZCoarse Graining: rz exact relation selected
-- statement:
--   The actual canonical correction relation from a proved map equality,
--   without changing the original global parity convention or correction rule.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L789-L805
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FourDimensionalToricCode/Decoder/RZCoarseGraining.lean#L789-L805

import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_Multiscale
import Definitions.Def_QEC_Coding_FourDimensionalToricCode_Decoder_RZCoarseGraining
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.MultiscaleDecoder QEC.Coding.MultiscaleDecoder.RZCoarseGraining
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

theorem QEC.Coding.MultiscaleDecoder.RZCoarseGraining.rz_exact_relation_selected
    (A : RZCoarseGrainingData D i V)
    (hcoh : LocalTopCohomologyIdentification A)
    (hcompat : InducedCoboundaryCompatibility A)
    (hselected : D.selectedMap i = D.rzMap i)
    (sigma : UpperSyndrome D i) :
    (sigma : D.family.Cochain2 i.succ) =
      D.family.coboundary1 i.succ (correctionFromSyndrome A hcoh sigma.1) +
        (D.selectedMap i).map2 (coarseSyndrome A hcompat sigma) := by sorry
