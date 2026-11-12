-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitABasisSupport_negativeABornWeight_le_traceDistance_to_aZero
-- name    : QEC.Distillation.OneQubitABasisSupport.negativeABornWeight_le_traceDistance_to_aZero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:00:10.885758+00:00
-- url     : https://prove2.me/theorems/5b7bf33e-608a-4447-a8e7-02bb0dcc767b
-- title:
--   One Qubit ABasis Support: negative ABorn Weight le trace Distance to a Zero
-- statement:
--   The literal negative-A Born probability of a physical qubit density is
--   bounded by its trace norm distance from the ideal `A₀` density.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPortSupport.lean#L158-L192
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPortSupport.lean#L158-L192

import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Semantics_Channels_TraceNorm
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SelectedPortSupport
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitABasisSupport
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit

theorem QEC.Distillation.OneQubitABasisSupport.negativeABornWeight_le_traceDistance_to_aZero
    (rho : DensityOperator QubitSpace) :
    aBasisInstrument.bornWeight .negative rho ≤
      traceNorm (rho.toOperator - aZeroDensity.toOperator) := by sorry
