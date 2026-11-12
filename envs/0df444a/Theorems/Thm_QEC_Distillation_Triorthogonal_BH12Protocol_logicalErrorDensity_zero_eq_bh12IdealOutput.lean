-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalErrorDensity_zero_eq_bh12IdealOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalErrorDensity_zero_eq_bh12IdealOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:10:08.593038+00:00
-- url     : https://prove2.me/theorems/e0ea04f7-4596-4507-98b8-c4391416f63e
-- title:
--   BH12 Protocol: logical Error Density zero eq bh12 Ideal Output
-- statement:
--   The BH12 Protocol construction uses the logical Error Density zero eq bh12 Ideal Output property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2999-L3004
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2999-L3004

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalErrorDensity_zero_eq_bh12IdealOutput (q : Nat) :
    logicalErrorDensity (0 : Word (ZMod 2) (OddRow q)) =
      bh12IdealOutput q := by sorry
