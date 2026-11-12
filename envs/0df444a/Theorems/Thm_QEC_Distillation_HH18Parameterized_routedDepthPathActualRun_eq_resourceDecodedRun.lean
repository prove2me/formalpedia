-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathActualRun_eq_resourceDecodedRun
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_resourceDecodedRun
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:35:55.810804+00:00
-- url     : https://prove2.me/theorems/5b49fd32-d046-4afe-81d9-fa97b4acb124
-- title:
--   HH18 Parameterized: routed Depth Path Actual Run eq resource Decoded Run
-- statement:
--   A path-indexed actual run is the literal one-level decoded run at that
--   path's independently selected physical rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L775-L783
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathEnvelope.lean#L775-L783

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathActualRun_eq_resourceDecodedRun {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) (path : routedDepthOutputSlots m w depth) :
    routedDepthPathActualRun h hdegree epsilon hsmall depth path =
      resourceDecodedRun h hdegree (noisyResources m w
        (routedDepthPathRate h hdegree epsilon hsmall depth path)) := by sorry
