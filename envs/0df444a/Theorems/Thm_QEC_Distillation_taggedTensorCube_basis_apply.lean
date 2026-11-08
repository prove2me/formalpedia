-- Prove2me | Theorems.Thm_QEC_Distillation_taggedTensorCube_basis_apply
-- name    : QEC.Distillation.taggedTensorCube_basis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:42:18.423829+00:00
-- url     : https://prove2.me/theorems/f66f4092-d4b9-4528-8732-15dfb851bc35
-- title:
--   Distillation: tagged Tensor Cube basis apply
-- statement:
--   The Distillation construction uses the tagged Tensor Cube basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L94-L111
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L94-L111

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

theorem QEC.Distillation.taggedTensorCube_basis_apply
    (f : ComputationalBasisRegister F J →ₗ[Complex] ComputationalBasisRegister F K)
    (u : TaggedThreeCopyRegisterLabel F J) (v : TaggedThreeCopyRegisterLabel F K) :
    taggedTensorCube F J K f (EuclideanSpace.basisFun _ Complex u) v =
      f (EuclideanSpace.basisFun _ Complex (extractBlock u .first)) (extractBlock v .first) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .second)) (extractBlock v .second) *
        f (EuclideanSpace.basisFun _ Complex (extractBlock u .third)) (extractBlock v .third) := by sorry
