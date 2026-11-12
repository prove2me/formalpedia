-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_errorBranch_check_eigen
-- name    : QEC.Distillation.HH18SyndromeDecoding.errorBranch_check_eigen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:45:23.001084+00:00
-- url     : https://prove2.me/theorems/2bd90d76-78be-486f-8314-96698dcd32a3
-- title:
--   HH18 Syndrome Decoding: error Branch check eigen
-- statement:
--   The concrete Z-error branch has exactly its derived signed check eigenvalues.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L191-L256
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L191-L256

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SitewisePhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_SyndromeDecoding
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18SyndromeDecoding
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18SyndromeDecoding.errorBranch_check_eigen (error : PhysicalErrorWord)
    (check : CheckIndex) :
    toHermitianQubitOperator
        (HH18PuncturedReedMuller.checkGenerator 0 1 4 check)
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) =
      (measuredSyndrome error check).sign •
        HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by sorry
