-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedEncodingIsometry_eq_tensorCube
-- name    : QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_eq_tensorCube
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:09:40.448071+00:00
-- url     : https://prove2.me/theorems/cf231dd2-97fe-4f4f-9470-858cf20d75c0
-- title:
--   Ngu24 Binary: binary Tagged Encoding Isometry eq tensor Cube
-- statement:
--   Full operator identification with the actual one-block encoder's literal tensor cube.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L63-L80
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L63-L80

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

theorem QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_eq_tensorCube (i : Nat)
    (psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i))) :
    binaryTaggedEncodingIsometry i psi =
      taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
        ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi := by sorry
