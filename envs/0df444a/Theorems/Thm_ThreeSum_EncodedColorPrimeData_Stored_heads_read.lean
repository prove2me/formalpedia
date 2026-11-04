-- Prove2me | Theorems.Thm_ThreeSum_EncodedColorPrimeData_Stored_heads_read
-- name    : ThreeSum.EncodedColorPrimeData.Stored.heads_read
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:46:02.528424+00:00
-- url     : https://prove2.me/theorems/488060bc-fcf2-4e7b-8e1e-c4af07fb4dfc
-- title:
--   Stored: heads read
-- statement:
--   The Stored construction uses the heads read property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeData.lean#L22-L35
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/EncodedColorPrimeData.lean#L22-L35

import Definitions.Def_Submission_ThreeSum_LightBandPrimeDepth
import Definitions.Def_Submission_ThreeSum_LightBandPrimeConstruction
import Definitions.Def_Submission_ThreeSum_EncodedColorPrimeData
set_option autoImplicit false
open ThreeSum ThreeSum.EncodedColorPrimeData
open Light

theorem ThreeSum.EncodedColorPrimeData.Stored.heads_read {μ : ℕ → ℤ} {free M y : ℕ} {qs : ℕ → ℕ} (H : Stored μ free M y qs) :
    μ free=(qs (LightBandPrimeDepth.depth M y) : ℤ) ∧
    μ (free+1)=(LightBandPrimeDepth.depth M y : ℤ) ∧
    μ (free+2)=(nextFree free M y : ℤ) ∧
    μ (free+3)=(poolBase free : ℤ) ∧
    μ (free+4)=(LightPrimePool.size y : ℤ) ∧
    μ (free+5)=(prefixBase free y : ℤ) := by sorry
