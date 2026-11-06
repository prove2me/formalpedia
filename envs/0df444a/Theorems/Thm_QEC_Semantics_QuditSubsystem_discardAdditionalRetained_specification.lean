-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_discardAdditionalRetained_specification
-- name    : QEC.Semantics.QuditSubsystem.discardAdditionalRetained_specification
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:46:33.312024+00:00
-- url     : https://prove2.me/theorems/7287c18f-60a1-4c25-a82c-b657ff43554f
-- title:
--   Qudit Subsystem: discard Additional Retained specification
-- statement:
--   The additional-retained discard is concretely factorization, swap, and raw CPTP partial trace.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L733-L741
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditSubsystem.lean#L733-L741

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

theorem QEC.Semantics.QuditSubsystem.discardAdditionalRetained_specification (S T : QuditSubsystem q)
    (hST : S.selected ⊆ T.selected) :
    S.discardAdditionalRetained T hST =
      QuantumChannel.comp
        (partialTraceRightRaw_cptp T.complementSystem (S.additionalRetainedSystem T))
        (QuantumChannel.comp
          (QuantumChannel.unitaryConj (S.additionalRetainedFactorSwap T))
          (QuantumChannel.unitaryConj (S.complementFactorization T hST))) := by sorry
