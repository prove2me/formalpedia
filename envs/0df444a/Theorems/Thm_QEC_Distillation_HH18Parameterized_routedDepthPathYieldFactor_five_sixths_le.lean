-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_five_sixths_le
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_five_sixths_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:06:00.826729+00:00
-- url     : https://prove2.me/theorems/7dfae508-b8be-4cd0-9a4b-61be36706df4
-- title:
--   HH18 Parameterized: routed Depth Path Yield Factor five sixths le
-- statement:
--   The actual finite fresh-stage accounting product is uniformly bounded
--   below by five sixths; this is a pathwise accounting result rather than a
--   joint-event construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L197-L241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L197-L241

import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathEnvelope
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_PathYield
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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_five_sixths_le {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    (5 / 6 : ℝ) ≤ (routedDepthPathYieldFactor h hdegree epsilon hsmall depth path : ℝ) := by sorry
