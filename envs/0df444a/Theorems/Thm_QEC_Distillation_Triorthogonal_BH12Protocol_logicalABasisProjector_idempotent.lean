-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_idempotent
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_idempotent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:33.338195+00:00
-- url     : https://prove2.me/theorems/a2f3fd6e-e60e-4505-9d2f-18a53ba46614
-- title:
--   BH12 Protocol: logical ABasis Projector idempotent
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Projector idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2684-L2692
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2684-L2692

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_idempotent {q : Nat} (a : OddRow q)
    (outcome : StabilizerOutcome) :
    logicalABasisProjector a outcome * logicalABasisProjector a outcome =
      logicalABasisProjector a outcome := by sorry
