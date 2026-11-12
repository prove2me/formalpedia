-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitMagic_sourceTSin_mul_sourceTCos
-- name    : QEC.Distillation.OneQubitMagic.sourceTSin_mul_sourceTCos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-10T12:25:36.204977+00:00
-- url     : https://prove2.me/theorems/b1573248-c448-4302-9722-28df3d6dd0fc
-- title:
--   One Qubit Magic: source TSin mul source TCos
-- statement:
--   The One Qubit Magic construction uses the source TSin mul source TCos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L87-L90
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/TResourcePhase.lean#L87-L90

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct

theorem QEC.Distillation.OneQubitMagic.sourceTSin_mul_sourceTCos :
    sourceTSin * sourceTCos = sourceTParameter / Real.sqrt 2 := by sorry
