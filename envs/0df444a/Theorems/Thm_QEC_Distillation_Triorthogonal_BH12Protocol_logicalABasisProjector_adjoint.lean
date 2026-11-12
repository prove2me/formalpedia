-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_logicalABasisProjector_adjoint
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_adjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:09:22.381019+00:00
-- url     : https://prove2.me/theorems/cd690bf0-aed1-46ee-8461-46dbff997158
-- title:
--   BH12 Protocol: logical ABasis Projector adjoint
-- statement:
--   The BH12 Protocol construction uses the logical ABasis Projector adjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2663-L2682
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2663-L2682

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.logicalABasisProjector_adjoint {q : Nat} (a : OddRow q)
    (outcome : StabilizerOutcome) :
    LinearMap.adjoint (logicalABasisProjector a outcome) =
      logicalABasisProjector a outcome := by sorry
