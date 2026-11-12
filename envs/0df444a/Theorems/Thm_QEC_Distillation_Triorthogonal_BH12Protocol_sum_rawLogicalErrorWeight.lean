-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_sum_rawLogicalErrorWeight
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.sum_rawLogicalErrorWeight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:05:33.843389+00:00
-- url     : https://prove2.me/theorems/23baa762-1c7e-43c4-8bf8-94cc490c5172
-- title:
--   BH12 Protocol: sum raw Logical Error Weight
-- statement:
--   Summing decoded logical words recovers the raw accepted mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1912-L1923
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1912-L1923

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.sum_rawLogicalErrorWeight (q : Nat) (p : ErrorParameter) :
    ∑ logical : Word (ZMod 2) (OddRow q),
        rawLogicalErrorWeight q p logical = rawSuccessMass q p := by sorry
