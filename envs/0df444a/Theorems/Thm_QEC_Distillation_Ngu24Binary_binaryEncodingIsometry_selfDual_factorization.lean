-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodingIsometry_selfDual_factorization
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:34:52.644927+00:00
-- url     : https://prove2.me/theorems/5cd92d7f-7d85-4513-9aba-803722f70805
-- title:
--   Ngu24 Binary: binary Encoding Isometry self Dual factorization
-- statement:
--   The actual binary encoder has the self-dual/MFE concatenation in source order.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L102-L110
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L102-L110

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_BinaryConversion
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinarySelfDual
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary.binarySelfDualFieldWordFintype

theorem QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_factorization (i : Nat) :
    (binaryEncodingIsometry i).toLinearMap =
      (mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
        ((selfDualIsometry (f256SourceInput i).PivotComplement).toLinearMap.comp
          ((f256SourceInput i).encodingLinearMap.comp
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i))).toLinearMap)) := by sorry
