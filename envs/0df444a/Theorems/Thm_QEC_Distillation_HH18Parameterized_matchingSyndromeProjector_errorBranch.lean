-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_matchingSyndromeProjector_errorBranch
-- name    : QEC.Distillation.HH18Parameterized.matchingSyndromeProjector_errorBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:43:34.031998+00:00
-- url     : https://prove2.me/theorems/7abc9daf-79a0-4a23-9e82-207894fdc8a8
-- title:
--   HH18 Parameterized: matching Syndrome Projector error Branch
-- statement:
--   The matching joint-syndrome projector fixes the actual physical error branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L249-L263
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L249-L263

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Syndrome
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.HH18Parameterized.matchingSyndromeProjector_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (HH18PuncturedReedMuller.checkGenerator_commutes h)
        (measuredSyndrome w r m error)
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) =
      HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree) := by sorry
