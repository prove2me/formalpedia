-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryFamily_tensor_intertwining
-- name    : QEC.Distillation.Ngu24Binary.binaryFamily_tensor_intertwining
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:36:57.648103+00:00
-- url     : https://prove2.me/theorems/5ce19341-ed81-4880-9393-a9e195a4027a
-- title:
--   Ngu24 Binary: binary Family tensor intertwining
-- statement:
--   The family equation through the literal tensor cube, for every logical state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L40-L50
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryFamily.lean#L40-L50

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

theorem QEC.Distillation.Ngu24Binary.binaryFamily_tensor_intertwining (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryPhysicalCCZ
        (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
          ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
          (binaryLogicalCCZ psi) := by sorry
