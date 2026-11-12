-- Prove2me | Theorems.Thm_QEC_Distillation_OneQubitABasisSupport_aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
-- name    : QEC.Distillation.OneQubitABasisSupport.aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:59:53.225424+00:00
-- url     : https://prove2.me/theorems/7abfca3d-1417-4e1d-993b-78c9f8ffbf67
-- title:
--   One Qubit ABasis Support: a Basis Dephasing map Density eq diagonal AResource at measured Rate
-- statement:
--   A-basis dephasing is exactly the diagonal A resource at its measured
--   negative-A Born rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPortSupport.lean#L271-L285
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SelectedPortSupport.lean#L271-L285

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

theorem QEC.Distillation.OneQubitABasisSupport.aBasisDephasing_mapDensity_eq_diagonalAResource_at_measuredRate
    (rho : DensityOperator QubitSpace) (p : ErrorParameter)
    (hrate : p.rate = aBasisInstrument.bornWeight .negative rho) :
    aBasisDephasing.mapDensity rho = diagonalAResource p := by sorry
