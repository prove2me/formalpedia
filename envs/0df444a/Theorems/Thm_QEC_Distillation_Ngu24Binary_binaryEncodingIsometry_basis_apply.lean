-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodingIsometry_basis_apply
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:02:07.470381+00:00
-- url     : https://prove2.me/theorems/e6d49f5b-4f83-465d-af49-0aaa2ad9c866
-- title:
--   Ngu24 Binary: binary Encoding Isometry basis apply
-- statement:
--   The Ngu24 Binary construction uses the binary Encoding Isometry basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L21-L30
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L21-L30

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

theorem QEC.Distillation.Ngu24Binary.binaryEncodingIsometry_basis_apply (i : Nat)
    (u : Word (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (v : Word (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512)) :
    binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex u) v =
      SourceInput.cosetNormalization (f256SourceInput i).H0 *
        ∑ h : (f256SourceInput i).H0,
          EuclideanSpace.basisFun _ Complex (binaryCosetWordMap i (u, h)) v := by sorry
