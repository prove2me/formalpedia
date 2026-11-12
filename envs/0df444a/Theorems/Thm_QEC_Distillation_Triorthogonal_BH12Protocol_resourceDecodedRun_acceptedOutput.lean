-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_acceptedOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:52:42.362194+00:00
-- url     : https://prove2.me/theorems/15a42103-a80e-4e72-8cd3-f4cce1bdccca
-- title:
--   BH12 Protocol: resource Decoded Run accepted Output
-- statement:
--   At positive accepted Born weight, the generic run's accepted output is the
--   actual BH12 decoded conditional rather than an interface completion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1843-L1850
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L1843-L1850

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_acceptedOutput (q : Nat)
    (inputs : ResourceInput (resourceCount q) Qubit.QubitSpace)
    (hpos : 0 < resourceEndpointWeight q inputs .accepted) :
    (resourceDecodedRun q inputs).acceptedOutput =
      resourceAcceptedOutput q inputs hpos := by sorry
