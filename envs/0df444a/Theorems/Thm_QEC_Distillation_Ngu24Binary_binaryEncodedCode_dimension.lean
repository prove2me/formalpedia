-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_binaryEncodedCode_dimension
-- name    : QEC.Distillation.Ngu24Binary.binaryEncodedCode_dimension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T11:43:21.022123+00:00
-- url     : https://prove2.me/theorems/19b6576f-bf01-411d-b537-4e392a651117
-- title:
--   Ngu24 Binary: binary Encoded Code dimension
-- statement:
--   The Ngu24 Binary construction uses the binary Encoded Code dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L86-L91
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/MultiplicativeQuditProtocol/BinaryEncoding.lean#L86-L91

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

theorem QEC.Distillation.Ngu24Binary.binaryEncodedCode_dimension (i : Nat) :
    (binaryEncodedCode i).code.dimension = 2 ^ f256MultiplicationLogicalCount i := by sorry
