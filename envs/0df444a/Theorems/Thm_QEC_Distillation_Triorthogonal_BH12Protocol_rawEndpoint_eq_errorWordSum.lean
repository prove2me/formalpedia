-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawEndpoint_eq_errorWordSum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawEndpoint_eq_errorWordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:53:38.700966+00:00
-- url     : https://prove2.me/theorems/44614b99-f7fc-4fb4-8a9e-8f3311e0304d
-- title:
--   BH12 Protocol: raw Endpoint eq error Word Sum
-- statement:
--   Raw physical endpoints are the corresponding independent error-word sums.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L604-L617
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L604-L617

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawEndpoint_eq_errorWordSum (q : Nat) (p : ErrorParameter)
    (outcome : DistillationOutcome) :
    rawEndpoint q p outcome =
      ∑ error : PhysicalError q,
        if syndromeOutcome (syndromeOfError error) = outcome then
          (errorWordProbability p error : Complex) •
            (errorBranchDensity error).toOperator
        else 0 := by sorry
