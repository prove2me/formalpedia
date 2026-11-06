-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_card_selected_le_total
-- name    : QEC.Semantics.QuditSubsystem.card_selected_le_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:45:35.468421+00:00
-- url     : https://prove2.me/theorems/5100413d-8e94-4b9b-b936-4ec00190a61c
-- title:
--   Qudit Subsystem: card selected le total
-- statement:
--   A selected finite coordinate set has cardinality at most the full coordinate type.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L269-L271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L269-L271

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

theorem QEC.Semantics.QuditSubsystem.card_selected_le_total (S : QuditSubsystem q) :
    Fintype.card S.SelectedCoordinates ≤ Fintype.card ι := by sorry
