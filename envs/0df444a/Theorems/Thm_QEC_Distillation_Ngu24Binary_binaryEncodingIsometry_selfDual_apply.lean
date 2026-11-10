-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodingIsometry_selfDual_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:35:00.443203+00:00
-- url     : https://prove2.me/theorems/49d9474a-e1c8-4133-9eb9-804c575e4e46
-- title:
--   Ngu24 Binary: binary Encoding Isometry self Dual apply
-- statement:
--   The source-ordered factorization evaluated on an arbitrary logical state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L113-L120
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L113-L120

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

theorem QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_selfDual_apply (i : Nat)
    (psi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i))) :
    binaryEncodingIsometry i psi =
      mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
        (selfDualIsometry (f256SourceInput i).PivotComplement
          ((f256SourceInput i).encodingLinearMap
            (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) psi))) := by sorry
