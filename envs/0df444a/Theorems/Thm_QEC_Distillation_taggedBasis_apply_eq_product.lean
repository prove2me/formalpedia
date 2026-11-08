-- Prove2me | Theorems.Thm_QEC_Distillation_taggedBasis_apply_eq_product
-- name    : QEC.Distillation.taggedBasis_apply_eq_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-07T05:41:33.927585+00:00
-- url     : https://prove2.me/theorems/6af16f00-08b0-4f8a-afcc-7bb5a4ca0135
-- title:
--   Distillation: tagged Basis apply eq product
-- statement:
--   A tagged computational ket is exactly the product of its three block kets.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L41-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/TensorRegister.lean#L41-L62

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_Register
import Definitions.Def_QEC_Semantics_Core_ComputationalTensor
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_TensorRegister
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation
open Semantics
open scoped TensorProduct BigOperators
variable (F J K : Type) [Fintype F] [Fintype J] [Fintype K] [DecidableEq J] [DecidableEq K]

theorem QEC.Distillation.taggedBasis_apply_eq_product (u v : TaggedThreeCopyRegisterLabel F J) :
    EuclideanSpace.basisFun _ Complex u v =
      EuclideanSpace.basisFun (J → F) Complex (extractBlock u .first) (extractBlock v .first) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .second) (extractBlock v .second) *
        EuclideanSpace.basisFun (J → F) Complex (extractBlock u .third) (extractBlock v .third) := by sorry
