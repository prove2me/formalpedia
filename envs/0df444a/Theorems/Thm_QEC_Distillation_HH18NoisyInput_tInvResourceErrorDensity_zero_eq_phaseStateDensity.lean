-- Prove2me | Theorems.Thm_QEC_Distillation_HH18NoisyInput_tInvResourceErrorDensity_zero_eq_phaseStateDensity
-- name    : QEC.Distillation.HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:31:12.213661+00:00
-- url     : https://prove2.me/theorems/63909410-bb11-430b-b0f1-4d30116c72a6
-- title:
--   HH18 Noisy Input: t Inv Resource Error Density zero eq phase State Density
-- statement:
--   The zero-error resource is the exact `T†` phase-injection density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L128-L130
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/NoisyInput.lean#L128-L130

import Definitions.Def_QEC_Coding_Stabilizer_PauliSemantics
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PuncturedReedMuller
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase
import Definitions.Def_QEC_Semantics_Entropy_Convexity
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18NoisyInput
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open OneQubitMagic
open scoped BigOperators
universe u

theorem QEC.Distillation.HH18NoisyInput.tInvResourceErrorDensity_zero_eq_phaseStateDensity :
    tInvResourceErrorDensity 0 = OneQubitMagic.phaseStateDensity (-Real.pi / 4) := by sorry
