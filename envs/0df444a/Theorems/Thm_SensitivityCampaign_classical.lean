-- Prove2me | Theorems.Thm_SensitivityCampaign_classical
-- name    : SensitivityCampaign.classical
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-16T01:36:35.10314+00:00
-- url     : https://prove2.me/theorems/22c7a0a5-0017-428b-bdff-f599fd24a5ed
-- title:
--   Classical separation exponent at least 2
-- statement:
--   For every real ε > 0 and integer S ≥ 2, there exist n and a total Boolean function f on n bits such that s(f) ≥ S and bs(f) ≥ s(f)^(2−ε).
-- source:
--   David Rubinstein, Sensitivity vs. block sensitivity of Boolean functions, Combinatorica 15 (1995), 297–299, https://doi.org/10.1007/BF01200762; Theorem 1 recalled in https://arxiv.org/abs/1008.0521

import Mathlib
import Definitions.Def_SensitivityCampaign

namespace SensitivityCampaign
theorem classical : AchievesExponent (2 : ℝ) := by sorry
end SensitivityCampaign
