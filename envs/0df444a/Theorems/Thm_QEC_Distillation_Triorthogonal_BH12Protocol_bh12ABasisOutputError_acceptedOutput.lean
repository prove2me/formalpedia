-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_bh12ABasisOutputError_acceptedOutput
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.bh12ABasisOutputError_acceptedOutput
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:55:10.595918+00:00
-- url     : https://prove2.me/theorems/732125b0-fdc6-457e-aa24-4219aa6e82dd
-- title:
--   BH12 Protocol: bh12 ABasis Output Error accepted Output
-- statement:
--   The state-dependent A-basis error of the actual accepted density against
--   the ideal logical magic state is exactly the source marginal enumerator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3236-L3248
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3236-L3248

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.bh12ABasisOutputError_acceptedOutput (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p)
    (a : OddRow q) :
    bh12ABasisOutputError a
        (resourceDecodedRun q (noisyResources q p)).acceptedOutput
        (bh12IdealOutput q) =
      decodedMarginalError q p hsuccess a := by sorry
