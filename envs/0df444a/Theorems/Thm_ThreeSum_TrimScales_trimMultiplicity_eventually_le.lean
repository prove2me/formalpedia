-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_trimMultiplicity_eventually_le
-- name    : ThreeSum.TrimScales.trimMultiplicity_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:09.815274+00:00
-- url     : https://prove2.me/theorems/0d0febfc-ec67-4ad4-8653-05ec52d5cbc6
-- title:
--   Trim Scales: trim Multiplicity eventually le
-- statement:
--   The Trim Scales construction uses the trim Multiplicity eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L164-L166
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L164-L166

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.trimMultiplicity_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (trimMultiplicity n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) := by sorry
