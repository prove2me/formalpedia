-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_tagged_intertwining
-- name    : QEC.Distillation.Ngu24Binary.binaryFamily_tagged_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:37:02.841229+00:00
-- url     : https://prove2.me/theorems/dc66f6ef-3670-4b84-a60c-0b1b4fad4dbd
-- title:
--   Ngu24 Binary: binary Family tagged intertwining
-- statement:
--   Specialization of the full source intertwining to the actual tower family.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L26-L37
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L26-L37

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryParameters
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryCubicBridge
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

theorem QEC.Distillation.Ngu24Binary.binaryFamily_tagged_intertwining (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryPhysicalCCZ (binaryTaggedEncodingLinearMap i psi) =
      binaryTaggedEncodingLinearMap i (binaryLogicalCCZ psi) := by sorry
