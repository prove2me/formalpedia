-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_operation
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_operation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:45:49.881975+00:00
-- url     : https://prove2.me/theorems/047b78b6-e67b-4c48-a1bd-d582997d9ccb
-- title:
--   BH12 Protocol: resource Decoded Run operation
-- statement:
--   The decoded run uses the existing parameter-free consumer, syndrome, and
--   decoder composition.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1836-L1839
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1836-L1839

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_operation (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace) :
    (resourceDecodedRun q inputs).operation = decodedOperation q := by sorry
