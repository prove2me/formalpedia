-- Prove2me | Theorems.Thm_ThreeSum_SubsetStages_stageValue_forced_prefix
-- name    : ThreeSum.SubsetStages.stageValue_forced_prefix
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:12:58.24939+00:00
-- url     : https://prove2.me/theorems/01fdd52a-ee33-4b52-bc0c-bb23a5c534a2
-- title:
--   Subset Stages: stage Value forced prefix
-- statement:
--   A forced prefix can be read directly from its stored suffix stage.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L91-L95
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/SubsetStages.lean#L91-L95

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset

theorem ThreeSum.SubsetStages.stageValue_forced_prefix {L : ℕ} (f : Finset (Fin L) → ℤ)
    (j : ℕ) (pre tail : Finset (Fin L))
    (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j) :
    stageValue f j (pre ∪ tail) = ∑ x ∈ tail.powerset, f (pre ∪ x) := by sorry
