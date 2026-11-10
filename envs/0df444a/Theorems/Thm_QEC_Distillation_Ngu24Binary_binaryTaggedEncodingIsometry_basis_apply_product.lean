-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryTaggedEncodingIsometry_basis_apply_product
-- name    : QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_basis_apply_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:59:57.289201+00:00
-- url     : https://prove2.me/theorems/321ff890-574d-47ff-8d69-adb8e0ae608e
-- title:
--   Ngu24 Binary: binary Tagged Encoding Isometry basis apply product
-- statement:
--   The Ngu24 Binary construction uses the binary Tagged Encoding Isometry basis apply product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L32-L60
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryTensorEncoding.lean#L32-L60

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTaggedEncoding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryTensorEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS Ngu24MultiplicativeCCZ
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators

theorem QEC.Distillation.Ngu24Binary.binaryTaggedEncodingIsometry_basis_apply_product (i : Nat)
    (u : TaggedThreeCopyRegisterLabel (ZMod 2) (Fin (f256MultiplicationLogicalCount i)))
    (v : TaggedThreeCopyRegisterLabel (ZMod 2) ((f256SourceInput i).PivotComplement × Fin 512)) :
    binaryTaggedEncodingIsometry i (registerBasisKet u) v =
      binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .first))
          (extractBlock v .first) *
        binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .second))
          (extractBlock v .second) *
        binaryEncodingIsometry i (EuclideanSpace.basisFun _ Complex (extractBlock u .third))
          (extractBlock v .third) := by sorry
