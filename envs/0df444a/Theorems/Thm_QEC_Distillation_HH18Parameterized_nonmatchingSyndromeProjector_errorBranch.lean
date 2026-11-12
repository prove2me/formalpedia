-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_nonmatchingSyndromeProjector_errorBranch
-- name    : QEC.Distillation.HH18Parameterized.nonmatchingSyndromeProjector_errorBranch
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:58:09.327551+00:00
-- url     : https://prove2.me/theorems/d88b431f-0226-4f64-9f12-5107dd378d42
-- title:
--   HH18 Parameterized: nonmatching Syndrome Projector error Branch
-- statement:
--   Every nonmatching full syndrome gives the literal zero vector branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L266-L283
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/Syndrome.lean#L266-L283

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

theorem QEC.Distillation.HH18Parameterized.nonmatchingSyndromeProjector_errorBranch {w r m : Nat}
    (h : Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (syndrome : Syndrome w r m)
    (hne : syndrome ≠ measuredSyndrome w r m error) :
    jointStabilizerProjector
        (HH18PuncturedReedMuller.checkGenerator w r m)
        (HH18PuncturedReedMuller.checkGenerator_commutes h)
        syndrome
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree)) = 0 := by sorry
