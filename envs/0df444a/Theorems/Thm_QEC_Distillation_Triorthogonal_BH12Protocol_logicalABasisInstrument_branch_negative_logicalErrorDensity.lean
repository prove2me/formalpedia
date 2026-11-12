-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisInstrument_branch_negative_logicalErrorDensity
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisInstrument_branch_negative_logicalErrorDensity
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:54:28.550864+00:00
-- url     : https://prove2.me/theorems/357dd406-cec0-4e89-bf48-58dac64c4eb2
-- title:
--   BH12 Protocol: logical ABasis Instrument branch negative logical Error Density
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Instrument branch negative logical Error Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3105-L3123
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3105-L3123

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisInstrument_branch_negative_logicalErrorDensity {q : Nat}
    (a : OddRow q) (logical : Word (ZMod 2) (OddRow q)) :
    (logicalABasisInstrument a).branchOperator .negative
        (logicalErrorDensity logical).toOperator =
      if logical a = 0 then 0 else (logicalErrorDensity logical).toOperator := by sorry
