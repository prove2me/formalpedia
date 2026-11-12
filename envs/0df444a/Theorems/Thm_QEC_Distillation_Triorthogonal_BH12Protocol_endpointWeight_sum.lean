-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_endpointWeight_sum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T21:42:44.432857+00:00
-- url     : https://prove2.me/theorems/2963b2c3-6896-4f53-92a6-19145f1659fd
-- title:
--   BH12 Protocol: endpoint Weight sum
-- statement:
--   The BH12 Protocol construction uses the endpoint Weight sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L200-L206
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L200-L206

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.endpointWeight_sum (q : Nat) (p : ErrorParameter) :
    endpointWeight q p .accepted + endpointWeight q p .rejected = 1 := by sorry
