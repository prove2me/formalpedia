-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_physicalIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.physicalIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:40:26.155443+00:00
-- url     : https://prove2.me/theorems/36f123b8-e97c-4d0d-957b-84141929e26d
-- title:
--   Ngu24 Binary: physical Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the physical Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L67-L70
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L67-L70

import Definitions.Def_QEC_Semantics_Core_ComputationalEmbedding
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_NormalClosureFamily
import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_Selector
import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryEncoding
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
variable (J : Type)
variable [Fintype J] [DecidableEq J]
attribute [local instance] QEC.Distillation.Ngu24Binary._p2m_local_instance_3142684436_53

theorem QEC.Distillation.Ngu24Binary.physicalIsometry_basis (u : J → F256) :
    physicalIsometry J (EuclideanSpace.basisFun (J → F256) Complex u) =
      EuclideanSpace.basisFun ((J × Fin 512) → ZMod 2) Complex (physicalWordEmbedding J u) := by sorry
