-- Prove2me | Theorems.Thm_ThreeSum_TernaryJointType_CertifiedParameters_alpha_sum
-- name    : ThreeSum.TernaryJointType.CertifiedParameters.alpha_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T06:30:27.287976+00:00
-- url     : https://prove2.me/theorems/2a9f61a1-8b59-4954-a69f-ac041bc7751a
-- title:
--   Certified Parameters: alpha sum
-- statement:
--   The Certified Parameters construction uses the alpha sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L213-L214
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryJointType.lean#L213-L214

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

theorem ThreeSum.TernaryJointType.CertifiedParameters.alpha_sum : alpha0 + alpha1 + alpha2 = 1 := by sorry
