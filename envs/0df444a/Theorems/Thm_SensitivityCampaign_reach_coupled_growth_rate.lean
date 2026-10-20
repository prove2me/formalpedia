-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_coupled_growth_rate
-- name    : SensitivityCampaign.reach_coupled_growth_rate
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T05:56:43.995414+00:00
-- url     : https://prove2.me/theorems/c1f02995-03b8-4ed8-a33c-d63e01974264
-- title:
--   Exact growth-rate separation from coupled target and guard profiles
-- statement:
--   Set
--
--   $$\alpha=\frac{\log(201838849)}{\log(7922)}\approx2.1301247951906238118.$$
--
--   For every real $\varepsilon>0$ and every integer $S\ge2$, there exist a dimension $n$ and a total Boolean function $f:\{0,1\}^n\to\{0,1\}$ with
--
--   $$s(f)\ge S,\qquad bs(f)\ge s(f)^{\alpha-\varepsilon}.$$
--
--   The logarithmic quotient is the exact exponent; the decimal is only an approximation. Sensitivity and block sensitivity are maximized over all inputs, and sensitive blocks are nonempty and pairwise disjoint. Consequently every fixed exponent $c<\alpha$ occurs as a literal power separation for arbitrarily large sensitivity.
-- source:
--   Exact growth-rate endpoint derived from the accepted finite-family theorem https://prove2.me/theorems/ddfe4bf3-88be-4876-a196-33c20c0319ff, proof a2bc2cd0-3d7f-4028-9e06-e978e8b8eaf5 (username yousofy with Codex, 2026-10-20). It uses unchanged campaign definitions and the proved campaign finite-certificate theorem. The construction retains Robin Kothari/Codex and earlier OpenAI/community attribution; full details and provenance are in the accepted finite-family proof.

import Mathlib
import Definitions.Def_SensitivityCampaign

theorem SensitivityCampaign.reach_coupled_growth_rate :
    SensitivityCampaign.AchievesExponent
      (Real.log (201838849 : ℝ) / Real.log (7922 : ℝ)) := by sorry
