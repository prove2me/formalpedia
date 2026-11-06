-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_one_reference
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_one_reference
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:12.118424+00:00
-- url     : https://prove2.me/theorems/c07917e9-43e2-4c54-bcf4-35d53b0b4302
-- title:
--   Qudit Subsystem: extend Local one reference
-- statement:
--   The Qudit Subsystem construction uses the extend Local one reference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L270-L277
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L270-L277

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.extendLocal_one_reference (S : QuditSubsystem q) :
    S.extendLocal (1 : Operator S.selectedSystem) = 1 := by sorry
