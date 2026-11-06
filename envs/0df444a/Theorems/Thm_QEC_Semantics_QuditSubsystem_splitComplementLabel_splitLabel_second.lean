-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_splitComplementLabel_splitLabel_second
-- name    : QEC.Semantics.QuditSubsystem.splitComplementLabel_splitLabel_second
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:50:19.803951+00:00
-- url     : https://prove2.me/theorems/9ef0fd9b-5f96-4600-91b9-792d8bf9a1a8
-- title:
--   Qudit Subsystem: split Complement Label split Label second
-- statement:
--   The final component of the nested split is exactly the complement component of the `T` split.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L697-L701
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L697-L701

import Definitions.Def_QEC_Semantics_Channels_Core
import Mathlib.Analysis.InnerProductSpace.PiL2
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.splitComplementLabel_splitLabel_second (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) (labels : Qudit.Label q) :
    (S.splitComplementLabel T hST (S.splitLabel labels).2).2 = (T.splitLabel labels).2 := by sorry
