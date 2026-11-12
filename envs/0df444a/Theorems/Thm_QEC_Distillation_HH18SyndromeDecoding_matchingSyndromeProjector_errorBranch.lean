-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_matchingSyndromeProjector_errorBranch
-- name    : QEC.Distillation.HH18SyndromeDecoding.matchingSyndromeProjector_errorBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:44:35.756309+00:00
-- url     : https://prove2.me/theorems/b950f571-4dd6-455e-96dd-f1f43ae6eac0
-- title:
--   HH18 Syndrome Decoding: matching Syndrome Projector error Branch
-- statement:
--   The matching real joint-syndrome projector fixes the concrete error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L259-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L259-L274

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

theorem QEC.Distillation.HH18SyndromeDecoding.matchingSyndromeProjector_errorBranch
    (error : PhysicalErrorWord) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (HH18PuncturedReedMuller.checkGenerator_commutes
          HH18NoisyInput.hh18_15_1_0_admissible)
        (measuredSyndrome error)
        (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) =
      HH18NoisyInput.hh18PhysicalTInvErrorBranch error := by sorry
