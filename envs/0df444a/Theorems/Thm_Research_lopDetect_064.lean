-- Prove2me | Theorems.Thm_Research_lopDetect_064
-- name    : Research.lopDetect_064
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-06T18:48:05.967442+00:00
-- url     : https://prove2.me/theorems/d5cb422a-fc65-42a1-bc9f-53a4405dd254
-- title:
--   Lopsided triangle detection with saving 0.064
-- statement:
--   The existing deterministic Corollary 26 inner procedure solves the lopsided triangle detection instances used by Theorem 17 in O(n²/D^0.064), for D≥1 and D^18≤n. This sharpens the analysis of the verified program using its original preprocessing exponent gamma>0.064 and query exponent q<0.4278.
-- source:
--   Parameter refinement of https://github.com/anthropics/formal-math/blob/e1a4e6508154ea59f030480661590a9fe3018011/3sum-apsp/ThreeSumApsp/Sec4/Corollary26.lean

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_TimeClaims_Sec3_Definitions

set_option autoImplicit false
set_option relaxedAutoImplicit false
open ThreeSumApsp

theorem Research.lopDetect_064 : ∃ (C : ℝ) (T : ℕ → ℕ → ℕ → ℝ), 0 ≤ C ∧
    Light.lightModel.lopDetect T ∧ ∀ n D₀ : ℕ, 1 ≤ D₀ → D₀ ^ 18 ≤ n →
      T n D₀ (queryCap n D₀) ≤ C * ((n : ℝ) ^ 2 / (D₀ : ℝ) ^ (0.064 : ℝ)) := by sorry
