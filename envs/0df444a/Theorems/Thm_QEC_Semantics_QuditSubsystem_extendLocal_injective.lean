-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocal_injective
-- name    : QEC.Semantics.QuditSubsystem.extendLocal_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:53.627732+00:00
-- url     : https://prove2.me/theorems/690f0228-84b8-4930-8613-a791dab60751
-- title:
--   Qudit Subsystem: extend Local injective
-- statement:
--   Identity extension of selected local operators is injective.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L363-L367
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L363-L367

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

theorem QEC.Semantics.QuditSubsystem.extendLocal_injective (S : QuditSubsystem q) (hq : ∀ i, 0 < q i) :
    Function.Injective S.extendLocal := by sorry
