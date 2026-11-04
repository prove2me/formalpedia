-- Prove2me | Theorems.Thm_ThreeSum_WantedResidueKeys_total_raw_global
-- name    : ThreeSum.WantedResidueKeys.total_raw_global
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:51:15.082448+00:00
-- url     : https://prove2.me/theorems/41dc79a6-598c-442e-8c7e-55cd9f181e09
-- title:
--   Wanted Residue Keys: total raw global
-- statement:
--   The Wanted Residue Keys construction uses the total raw global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L59-L67
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L59-L67

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators

theorem ThreeSum.WantedResidueKeys.total_raw_global (M : ℕ) (P : ℤ) (xs : List ℤ) (h J : ℕ) (shift : ℤ) :
    total M (fun i => (RawAKeyLists.keys P xs).getD i 0)
      (fun j => (GlobalKeyEnumeration.globalKeys h J).getD j 0)
      (RawAKeyLists.keys P xs).length (GlobalKeyEnumeration.globalKeys h J).length shift =
    WantedPairs.count
      (fun i => LightResidues.residue M 1 ((RawAKeyLists.keys P xs).getD i 0+shift))
      (fun j => LightResidues.residue M 1 ((GlobalKeyEnumeration.globalKeys h J).getD j 0))
      (GlobalKeyEnumeration.globalKeys h J).length (RawAKeyLists.keys P xs).length := by sorry
