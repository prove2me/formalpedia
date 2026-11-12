-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_add
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:59.855422+00:00
-- url     : https://prove2.me/theorems/76944a94-424c-406d-b149-0641d921cb09
-- title:
--   BH12 Protocol: logical ABasis Projector add
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Projector add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2694-L2698
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2694-L2698

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_add {q : Nat} (a : OddRow q) :
    logicalABasisProjector a .positive +
      logicalABasisProjector a .negative = 1 := by sorry
