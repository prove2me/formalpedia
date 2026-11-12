-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12MagicStateDistillationProtocol_successfulOutputError
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_successfulOutputError
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:13:31.625375+00:00
-- url     : https://prove2.me/theorems/aeaf1030-221a-4f42-be70-c2ba8992cb60
-- title:
--   BH12 Protocol: bh12 Magic State Distillation Protocol successful Output Error
-- statement:
--   The packaged protocol exposes the already-derived accepted marginal,
--   rather than a target-shaped success or error field.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3266-L3270
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3266-L3270

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.bh12MagicStateDistillationProtocol_successfulOutputError (q : Nat)
    (p : ErrorParameter) (a : OddRow q) (hsuccess : 0 < rawSuccessMass q p) :
    (bh12MagicStateDistillationProtocol q p a hsuccess).successfulOutputError =
      decodedMarginalError q p hsuccess a := by sorry
