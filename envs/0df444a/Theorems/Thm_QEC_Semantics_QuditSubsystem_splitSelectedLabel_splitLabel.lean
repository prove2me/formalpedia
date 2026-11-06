-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_splitSelectedLabel_splitLabel
-- name    : QEC.Semantics.QuditSubsystem.splitSelectedLabel_splitLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T10:51:21.511859+00:00
-- url     : https://prove2.me/theorems/acad01fe-5466-44d9-9066-ca6bd4d9b615
-- title:
--   Qudit Subsystem: split Selected Label split Label
-- statement:
--   Splitting a global label through `T` agrees with the nested `S`, `T \ S`, and `Tᶜ` split.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L686-L694
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L686-L694

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

theorem QEC.Semantics.QuditSubsystem.splitSelectedLabel_splitLabel (S T : QuditSubsystem q) (hST : S.selected ⊆ T.selected)
    (labels : Qudit.Label q) :
    S.splitSelectedLabel T hST (T.splitLabel labels).1 =
      ((S.splitLabel labels).1, (S.splitComplementLabel T hST (S.splitLabel labels).2).1) := by sorry
