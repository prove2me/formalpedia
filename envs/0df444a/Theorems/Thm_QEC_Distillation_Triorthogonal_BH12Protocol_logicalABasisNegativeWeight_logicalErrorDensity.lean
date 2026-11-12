-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisNegativeWeight_logicalErrorDensity
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_logicalErrorDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:12:45.171794+00:00
-- url     : https://prove2.me/theorems/59f84559-2c75-4e37-9068-c75fca782e69
-- title:
--   BH12 Protocol: logical ABasis Negative Weight logical Error Density
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Negative Weight logical Error Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3159-L3170
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3159-L3170

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisNegativeWeight_logicalErrorDensity {q : Nat}
    (a : OddRow q) (logical : Word (ZMod 2) (OddRow q)) :
    logicalABasisNegativeWeight a (logicalErrorDensity logical) =
      if logical a = 0 then 0 else 1 := by sorry
