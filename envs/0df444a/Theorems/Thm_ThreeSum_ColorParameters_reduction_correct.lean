-- Prove2me | Theorems.Thm_ThreeSum_ColorParameters_reduction_correct
-- name    : ThreeSum.ColorParameters.reduction_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:33:29.673319+00:00
-- url     : https://prove2.me/theorems/96afef76-bf26-4dcd-a7a0-ec2a7a330c53
-- title:
--   Color Parameters: reduction correct
-- statement:
--   The Color Parameters construction uses the reduction correct property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorParameters.lean#L94-L102
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorParameters.lean#L94-L102

import Definitions.Def_Submission_ThreeSum_ColorClassLists
import Mathlib.Data.List.FinRange
import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_WeightedCache3SUM_Alias_a2077ae4d725396c
import Theorems.Thm_ThreeSum_Coloring_reduction_correct

set_option autoImplicit false
open ThreeSum ThreeSum.ColorParameters

theorem ThreeSum.ColorParameters.reduction_correct {n W : ℕ} (x : Fin n→ℤ) (hn : n ≤ 2^W) :
    Coloring.DistinctZeroSum x ↔
      ∃ t, ∃ ht : t < count W, ColorClassLists.witness (parameter ht) x := by sorry
