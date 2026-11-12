-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathRate_append_le_quarter
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:45:57.019883+00:00
-- url     : https://prove2.me/theorems/c26387fc-27df-41e4-b06b-8a1a73e7df77
-- title:
--   HH18 Parameterized: routed Depth Path Rate append le quarter
-- statement:
--   Every actual selected-port path contracts by a factor of four at each
--   successor, although different ports retain different literal rates.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L888-L900
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L888-L900

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathRate_append_le_quarter {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    {depth : Nat} (path : routedDepthOutputSlots m w depth)
    (port : LogicalSite m w) :
    (routedDepthPathRate h hdegree epsilon hsmall (depth + 1)
      (routedDepthOutputPathAppend m w depth path port)).1 ≤
        (routedDepthPathRate h hdegree epsilon hsmall depth path).1 / 4 := by sorry
