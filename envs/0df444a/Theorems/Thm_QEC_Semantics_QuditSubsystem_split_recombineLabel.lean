-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_split_recombineLabel
-- name    : QEC.Semantics.QuditSubsystem.split_recombineLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:20:08.287853+00:00
-- url     : https://prove2.me/theorems/24594bc4-ed48-417d-a3a1-a261c520c830
-- title:
--   Qudit Subsystem: split recombine Label
-- statement:
--   Splitting a recombined pair returns both selected and complement labels.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L250-L253
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L250-L253

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

theorem QEC.Semantics.QuditSubsystem.split_recombineLabel (S : QuditSubsystem q)
    (labels : Qudit.Label S.selectedDimensions × Qudit.Label S.complementDimensions) :
    S.splitLabel (S.recombineLabel labels) = labels := by sorry
