-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_logicalIsometry_basis
-- name    : QEC.Distillation.Ngu24Binary.logicalIsometry_basis
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:39:57.984783+00:00
-- url     : https://prove2.me/theorems/ec3e5a4b-0aa4-4020-bf96-13f993699245
-- title:
--   Ngu24 Binary: logical Isometry basis
-- statement:
--   The Ngu24 Binary construction uses the logical Isometry basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L62-L65
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L62-L65

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

theorem QEC.Distillation.Ngu24Binary.logicalIsometry_basis (u : J → ZMod 2) :
    logicalIsometry J (EuclideanSpace.basisFun (J → ZMod 2) Complex u) =
      EuclideanSpace.basisFun (J → F256) Complex (logicalWordEmbedding J u) := by sorry
