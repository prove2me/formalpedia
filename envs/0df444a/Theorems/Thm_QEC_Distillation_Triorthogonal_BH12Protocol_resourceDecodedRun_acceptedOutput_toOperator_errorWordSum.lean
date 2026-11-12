-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_acceptedOutput_toOperator_errorWordSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:53:49.675134+00:00
-- url     : https://prove2.me/theorems/f8d51cc7-2dc8-478f-8d84-05e4e624b9e1
-- title:
--   BH12 Protocol: resource Decoded Run accepted Output to Operator error Word Sum
-- statement:
--   At positive success mass, the supplied-resource run's accepted output is
--   the normalized mixture of the genuinely decoded logical error branches.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3018-L3046
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L3018-L3046

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

theorem QEC.Distillation.Triorthogonal.BH12Protocol.resourceDecodedRun_acceptedOutput_toOperator_errorWordSum (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) :
    (resourceDecodedRun q (noisyResources q p)).acceptedOutput.toOperator =
      ((rawSuccessMass q p : Complex)⁻¹) •
        ∑ error : PhysicalError q,
          if Accepts error then
            (errorWordProbability p error : Complex) •
              (logicalErrorDensity (logicalErrorWord error)).toOperator
          else 0 := by sorry
