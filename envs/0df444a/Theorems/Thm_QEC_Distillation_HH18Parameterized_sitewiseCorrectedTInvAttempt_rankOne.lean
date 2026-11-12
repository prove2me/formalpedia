-- Prove2me | Theorems.Thm_QEC_Distillation_HH18Parameterized_sitewiseCorrectedTInvAttempt_rankOne
-- name    : QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_rankOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T15:57:40.691641+00:00
-- url     : https://prove2.me/theorems/dc1bb9b3-dc19-4b5e-a155-4f2e37425d7a
-- title:
--   HH18 Parameterized: sitewise Corrected TInv Attempt rank One
-- statement:
--   The finite branch scalar cancels exactly in the rank-one pure-density
--   operator of the actual parameterized injection branch.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L317-L330
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/LowOverheadProtocol/Parameterized/SitewiseInjection.lean#L317-L330

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Preparation
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Core_PhaseInjection
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_SitewiseInjection
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.PauliSymplectic
open Semantics.Qubit
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite

theorem QEC.Distillation.HH18Parameterized.sitewiseCorrectedTInvAttempt_rankOne {w r m : Nat}
    (h : Coding.PuncturedReedMuller.Admissible w r m) (hdegree : 3 * r < m)
    (error : PhysicalErrorWord m w) (outcomes : InjectionOutcomeWord m w) :
    (InnerProductSpace.rankOne Complex
      (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))
      (sitewiseCorrectedTInvAttempt error outcomes (encodedLogicalPlus h))).toLinearMap =
      (InnerProductSpace.rankOne Complex
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))
        (HH18NoisyInput.zErrorOperator error (physicalTInvBranch h hdegree))).toLinearMap := by sorry
