-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathTypedOutputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathTypedOutputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:39:29.224086+00:00
-- url     : https://prove2.me/theorems/569c935d-0c8a-4e59-a4e6-7c6a4d33a3de
-- title:
--   HH18 Parameterized: routed Depth Path Typed Output Slots card
-- statement:
--   The routed logical output-slot carrier has the exact `k^z` cardinality
--   used by pathwise successful-output accounting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L252-L255
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L252-L255

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathTypedOutputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthOutputSlots m w depth) =
      logicalOutputCount m w ^ depth := by sorry
