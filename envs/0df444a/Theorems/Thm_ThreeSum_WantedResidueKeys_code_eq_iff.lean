-- Prove2me | Theorems.Thm_ThreeSum_WantedResidueKeys_code_eq_iff
-- name    : ThreeSum.WantedResidueKeys.code_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:54.76311+00:00
-- url     : https://prove2.me/theorems/e8ce9fc8-372b-470a-ad5f-6739a33cdef6
-- title:
--   Wanted Residue Keys: code eq iff
-- statement:
--   The Wanted Residue Keys construction uses the code eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L28-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L28-L31

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators

theorem ThreeSum.WantedResidueKeys.code_eq_iff {M : ℕ} (hM : 0 < M) (a b shift : ℤ) :
    code M 0 b=code M shift a ↔ (M : ℤ) ∣ a+shift-b := by sorry
