-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalIsometry_eq_selfDual_comp
-- name    : QEC.Distillation.Ngu24Binary.physicalIsometry_eq_selfDual_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:34:04.565723+00:00
-- url     : https://prove2.me/theorems/02c09516-9fef-43d9-81df-36ee1847e35c
-- title:
--   Ngu24 Binary: physical Isometry eq self Dual comp
-- statement:
--   Full linear-map factorization of the physical encoder through the source basis change.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L89-L99
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinarySelfDual.lean#L89-L99

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

theorem QEC.Distillation.Ngu24Binary.physicalIsometry_eq_selfDual_comp :
    (physicalIsometry J).toLinearMap =
      (mfeFromSelfDualIsometry J).toLinearMap.comp (selfDualIsometry J).toLinearMap := by sorry
