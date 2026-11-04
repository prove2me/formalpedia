-- Prove2me | Theorems.Thm_ThreeSum_LightPrimePool_values_nodup
-- name    : ThreeSum.LightPrimePool.values_nodup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T09:03:52.057075+00:00
-- url     : https://prove2.me/theorems/40a69caa-d6bd-49ce-afae-775e7795241d
-- title:
--   Light Prime Pool: values nodup
-- statement:
--   The Light Prime Pool construction uses the values nodup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L82-L82
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightPrimePool.lean#L82-L82

import Definitions.Def_Submission_ThreeSum_LightPrimality
import Definitions.Def_Submission_ThreeSum_PrimeDensity
import Definitions.Def_Submission_ThreeSum_WeightedScore
import Mathlib.NumberTheory.Bertrand
import Definitions.Def_Submission_ThreeSum_LightPrimePool
set_option autoImplicit false
open ThreeSum ThreeSum.LightPrimePool
open Light
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

theorem ThreeSum.LightPrimePool.values_nodup (y : ℕ) : (values y).Nodup := by sorry
