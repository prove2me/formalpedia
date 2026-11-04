-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_endpoint_marginals
-- name    : ThreeSum.TernaryJointType.CertifiedParameters.endpoint_marginals
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:30:29.121358+00:00
-- url     : https://prove2.me/theorems/b453f7b8-ad12-4314-97ff-bf64f569999b
-- title:
--   Certified Parameters: endpoint marginals
-- statement:
--   The Certified Parameters construction uses the endpoint marginals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L216-L219
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L216-L219

import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryJointType
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryJointType
open Finset
open ThreeSum.TernaryJointType.CertifiedParameters

theorem ThreeSum.TernaryJointType.CertifiedParameters.endpoint_marginals :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by sorry
