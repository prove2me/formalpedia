-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_eq_rawError
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_eq_rawError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:36:30.414094+00:00
-- url     : https://prove2.me/theorems/7acca9bb-1c63-47b5-8139-684e5ba051da
-- title:
--   HH18 Parameterized: routed Depth Path Rate append eq raw Error
-- statement:
--   Appending a selected port uses the literal selected-port Born error, with
--   the total selector's fallback branch proved unreachable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L641-L656
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L641-L656

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_eq_rawError {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port)).1 =
        selectedLogicalPortRawError h hdegree
          (routedDepthPathRate h hdegree epsilon hsmall depth path) port := by sorry
