-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawAcceptedEndpoint_eq_errorWordSum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawAcceptedEndpoint_eq_errorWordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:52:55.375671+00:00
-- url     : https://prove2.me/theorems/4fa5ab1a-de7a-4370-8df0-f14a757a44bb
-- title:
--   BH12 Protocol: raw Accepted Endpoint eq error Word Sum
-- statement:
--   The BH12 Protocol construction uses the raw Accepted Endpoint eq error Word Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L619-L631
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L619-L631

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawAcceptedEndpoint_eq_errorWordSum (q : Nat) (p : ErrorParameter) :
    rawEndpoint q p .accepted =
      ∑ error : PhysicalError q,
        if Accepts error then
          (errorWordProbability p error : Complex) •
            (errorBranchDensity error).toOperator
        else 0 := by sorry
