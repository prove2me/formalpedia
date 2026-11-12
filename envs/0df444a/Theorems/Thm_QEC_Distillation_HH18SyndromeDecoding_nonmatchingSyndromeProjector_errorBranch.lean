-- Prove2me | Theorems.Thm_QEC_Distillation_HH18SyndromeDecoding_nonmatchingSyndromeProjector_errorBranch
-- name    : QEC.Distillation.HH18SyndromeDecoding.nonmatchingSyndromeProjector_errorBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T16:46:25.598214+00:00
-- url     : https://prove2.me/theorems/fb8141ed-3dc1-4294-9043-dbc7bc9d520e
-- title:
--   HH18 Syndrome Decoding: nonmatching Syndrome Projector error Branch
-- statement:
--   Every nonmatching full syndrome gives the literal zero vector branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L277-L293
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Core/SyndromeDecoding.lean#L277-L293

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

theorem QEC.Distillation.HH18SyndromeDecoding.nonmatchingSyndromeProjector_errorBranch
    (error : PhysicalErrorWord) (syndrome : Syndrome)
    (hne : syndrome ≠ measuredSyndrome error) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator 0 1 4)
        (HH18PuncturedReedMuller.checkGenerator_commutes
          HH18NoisyInput.hh18_15_1_0_admissible)
        syndrome (HH18NoisyInput.hh18PhysicalTInvErrorBranch error) = 0 := by sorry
