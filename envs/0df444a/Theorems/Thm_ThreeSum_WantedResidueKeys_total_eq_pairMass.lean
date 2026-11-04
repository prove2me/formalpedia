-- Prove2me | Theorems.Thm_ThreeSum_WantedResidueKeys_total_eq_pairMass
-- name    : ThreeSum.WantedResidueKeys.total_eq_pairMass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:03:52.97685+00:00
-- url     : https://prove2.me/theorems/a234d51d-9f8e-4173-87f0-32d4f930b606
-- title:
--   Wanted Residue Keys: total eq pair Mass
-- statement:
--   The Wanted Residue Keys construction uses the total eq pair Mass property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L36-L44
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/WantedResidueKeys.lean#L36-L44

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators

theorem ThreeSum.WantedResidueKeys.total_eq_pairMass (M : ℕ) (hM : 0 < M) (left right : ℕ → ℤ)
    (NL NR : ℕ) (shift : ℤ) :
    total M left right NL NR shift =
      Histograms.pairMass (Finset.range NL) (Finset.range NR)
        (fun i => (left i : ZMod M)) (fun j => (right j : ZMod M))
        (fun _ => 1) (fun _ => 1) (shift : ZMod M) := by sorry
