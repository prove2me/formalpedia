-- Prove2me | Theorems.Thm_ThreeSum_LightZetaStages_stored_forced_lookup
-- name    : ThreeSum.LightZetaStages.stored_forced_lookup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:16:50.685431+00:00
-- url     : https://prove2.me/theorems/9372c727-08b9-4946-aa83-a59ce787146f
-- title:
--   Light Zeta Stages: stored forced lookup
-- statement:
--   The Light Zeta Stages construction uses the stored forced lookup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L202-L209
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightZetaStages.lean#L202-L209

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_LightZetaStages
set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}

theorem ThreeSum.LightZetaStages.stored_forced_lookup {μ : ℕ → ℤ} {L cut base j : ℕ}
    {f : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut f L) (hj : j ≤ L)
    (pre tail : Finset (Fin L)) (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j)
    (hcut : (pre ∪ tail).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank (pre ∪ tail)) =
      ∑ x ∈ tail.powerset, f (pre ∪ x) := by sorry
