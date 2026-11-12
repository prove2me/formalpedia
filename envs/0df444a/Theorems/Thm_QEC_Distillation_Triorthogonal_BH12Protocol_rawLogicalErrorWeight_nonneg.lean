-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawLogicalErrorWeight_nonneg
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:10.697493+00:00
-- url     : https://prove2.me/theorems/09f3f4af-ddea-49e3-afa9-313e7c0abf4a
-- title:
--   BH12 Protocol: raw Logical Error Weight nonneg
-- statement:
--   The BH12 Protocol construction uses the raw Logical Error Weight nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1902-L1909
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1902-L1909

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawLogicalErrorWeight_nonneg (q : Nat) (p : ErrorParameter)
    (logical : Word (ZMod 2) (OddRow q)) :
    0 ≤ rawLogicalErrorWeight q p logical := by sorry
