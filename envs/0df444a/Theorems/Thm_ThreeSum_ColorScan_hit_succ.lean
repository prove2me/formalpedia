-- Prove2me | Theorems.Thm_ThreeSum_ColorScan_hit_succ
-- name    : ThreeSum.ColorScan.hit_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:18:33.03685+00:00
-- url     : https://prove2.me/theorems/25d25f48-94ee-4b80-b115-bee9b844dd08
-- title:
--   Color Scan: hit succ
-- statement:
--   The Color Scan construction uses the hit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorScan.lean#L21-L31
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/ColorScan.lean#L21-L31

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_ColorScan
set_option autoImplicit false
open ThreeSum ThreeSum.ColorScan
open ColorParameters

theorem ThreeSum.ColorScan.hit_succ {n W t : ℕ} (x : Fin n → ℤ) (ht : t < count W) :
    Hit x W (t+1) ↔ Hit x W t ∨ ColorClassLists.witness (parameter ht) x := by sorry
