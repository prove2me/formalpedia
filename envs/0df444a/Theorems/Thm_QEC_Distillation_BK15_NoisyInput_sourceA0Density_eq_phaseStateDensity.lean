-- Prove2me | Theorems.Thm_QEC_Distillation_BK15_NoisyInput_sourceA0Density_eq_phaseStateDensity
-- name    : QEC.Distillation.BK15.NoisyInput.sourceA0Density_eq_phaseStateDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T00:58:49.747205+00:00
-- url     : https://prove2.me/theorems/07d5a712-88ff-455b-b0c6-52ea03019967
-- title:
--   Noisy Input: source A0 Density eq phase State Density
-- statement:
--   The source-order `K†`-then-`H` preparation is exactly `|A₀⟩`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L125-L133
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/FifteenQubitH/NoisyInput.lean#L125-L133

import Definitions.Def_QEC_Coding_Stabilizer_Measurement
import Definitions.Def_QEC_Distillation_FifteenQubitH_Code
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_Core_TransversalGate
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_FifteenQubitH_NoisyInput
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.NoisyInput
open Semantics Semantics.Qubit
open OneQubitMagic
open Coding.PauliSymplectic
open scoped BigOperators TensorProduct
universe u v w
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.BK15.NoisyInput.sourceA0Density_eq_phaseStateDensity :
    sourceA0Density = phaseStateDensity (Real.pi / 4) := by sorry
