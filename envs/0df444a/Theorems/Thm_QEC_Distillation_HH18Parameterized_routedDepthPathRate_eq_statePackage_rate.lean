-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_eq_statePackage_rate
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_eq_statePackage_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:03:14.066166+00:00
-- url     : https://prove2.me/theorems/70086732-6fe2-46ca-b599-5064334fa064
-- title:
--   HH18 Parameterized: routed Depth Path Rate eq state Package rate
-- statement:
--   The transparent selector is exactly the rate index of its packaged actual
--   routed-depth state.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L754-L761
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L754-L761

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_FreshDepth
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_eq_statePackage_rate {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathRate h hdegree epsilon hsmall depth path =
      (routedDepthPathStatePackage h hdegree epsilon hsmall depth path).rate := by sorry
