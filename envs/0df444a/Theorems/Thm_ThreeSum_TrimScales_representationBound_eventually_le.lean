-- Prove2me | Theorems.Thm_ThreeSum_TrimScales_representationBound_eventually_le
-- name    : ThreeSum.TrimScales.representationBound_eventually_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:53:08.848788+00:00
-- url     : https://prove2.me/theorems/5ad08712-ed5c-47dd-a421-ddb1f71c48bf
-- title:
--   Trim Scales: representation Bound eventually le
-- statement:
--   The Trim Scales construction uses the representation Bound eventually le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L248-L250
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TrimScales.lean#L248-L250

import Definitions.Def_Submission_ThreeSum_Scales
import Definitions.Def_Submission_ThreeSum_LocalHashMoments
import Definitions.Def_Submission_ThreeSum_TrimScales
set_option autoImplicit false
open ThreeSum ThreeSum.TrimScales
open Filter Real ThreeSum.Scales
open scoped Topology
noncomputable section

theorem ThreeSum.TrimScales.representationBound_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (representationBound n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) := by sorry
