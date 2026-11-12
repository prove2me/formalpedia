-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_one_eq_actualRootRunSuccess
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_one_eq_actualRootRunSuccess
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T20:07:43.807766+00:00
-- url     : https://prove2.me/theorems/d4f19a85-b0ee-42bf-bfec-7ff66f441576
-- title:
--   HH18 Parameterized: routed Depth Path Yield Factor one eq actual Root Run Success
-- statement:
--   At depth one, the sole stage of every output path is the genuine initial
--   parameterized HH18 run at the original physical input rate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L443-L454
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L443-L454

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathYieldFactor_one_eq_actualRootRunSuccess {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (path : routedDepthOutputSlots m w 1) :
    (routedDepthPathYieldFactor h hdegree epsilon hsmall 1 path : ℝ) =
      (resourceDecodedRun h hdegree (noisyResources m w epsilon)).successProbability := by sorry
