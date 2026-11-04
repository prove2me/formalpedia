-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedContraction_child_card_le
-- name    : ThreeSum.TernaryPairedContraction.child_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:08:04.362131+00:00
-- url     : https://prove2.me/theorems/fd1460c6-5d81-4da8-a6e2-e6b39fe3b918
-- title:
--   Ternary Paired Contraction: child card le
-- statement:
--   The Ternary Paired Contraction construction uses the child card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedContraction.lean#L19-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedContraction.lean#L19-L31

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedContraction
set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryPairedContraction
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem ThreeSum.TernaryPairedContraction.child_card_le (L m F : ℕ) (α π : DigitType) :
    Fintype.card (Child L m F α π) ≤ F*(vertices L π).card*(2^(π 1)*3^(π 2))^m := by sorry
