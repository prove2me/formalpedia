-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceAcceptedWeight_noisyResources_eq_rawSuccessMass
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedWeight_noisyResources_eq_rawSuccessMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:52:21.213008+00:00
-- url     : https://prove2.me/theorems/534f157c-efd2-4e55-9e7b-22842ad29314
-- title:
--   BH12 Protocol: resource Accepted Weight noisy Resources eq raw Success Mass
-- statement:
--   The supplied-resource accepted endpoint has exactly the proved BH12 raw success mass.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1644-L1648
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1644-L1648

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceAcceptedWeight_noisyResources_eq_rawSuccessMass (q : Nat)
    (p : ErrorParameter) :
    resourceEndpointWeight q (noisyResources q p) .accepted = rawSuccessMass q p := by sorry
