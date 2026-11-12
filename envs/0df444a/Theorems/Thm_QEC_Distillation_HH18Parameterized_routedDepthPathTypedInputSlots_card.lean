-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathTypedInputSlots_card
-- name    : QEC.Distillation.HH18Parameterized.routedDepthPathTypedInputSlots_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T19:43:53.731456+00:00
-- url     : https://prove2.me/theorems/755e0170-0240-4f94-bba6-964d657e976f
-- title:
--   HH18 Parameterized: routed Depth Path Typed Input Slots card
-- statement:
--   The routed physical input-slot carrier has the exact `n^z` cardinality
--   used by pathwise successful-output accounting.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L245-L248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/PathYield.lean#L245-L248

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

theorem QEC.Distillation.HH18Parameterized.routedDepthPathTypedInputSlots_card (m w depth : Nat) :
    Fintype.card (routedDepthInputSlots m w depth) =
      physicalInputCount m w ^ depth := by sorry
