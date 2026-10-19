-- Prove2me | Theorems.Thm_SensitivityCampaign_rubinstein_bounds
-- name    : SensitivityCampaign.rubinstein_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-16T01:36:12.434452+00:00
-- url     : https://prove2.me/theorems/ee2f9686-b078-4d78-b3ba-1869ba96f48c
-- title:
--   Rubinstein’s exact quadratic separation
-- statement:
--   For each integer m ≥ 1, there exists a total Boolean function f on (2m)² bits with s(f)=2m and bs(f)=2m². Both are global maxima over all inputs.
-- source:
--   David Rubinstein, Sensitivity vs. block sensitivity of Boolean functions, Combinatorica 15 (1995), 297–299, https://doi.org/10.1007/BF01200762; Theorem 1 recalled in https://arxiv.org/abs/1008.0521

import Mathlib
import Definitions.Def_SensitivityCampaign

namespace SensitivityCampaign
theorem rubinstein_bounds (m : ℕ) (hm : 1 ≤ m) :
    ∃ f : (Fin ((2 * m) ^ 2) → Bool) → Bool,
      OAI.Paper320.sensitivity f = 2 * m ∧
      OAI.Paper320.blockSensitivity f = 2 * m ^ 2 := by sorry
end SensitivityCampaign
