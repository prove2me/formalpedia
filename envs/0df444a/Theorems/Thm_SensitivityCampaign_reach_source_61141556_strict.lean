-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_source_61141556_strict
-- name    : SensitivityCampaign.reach_source_61141556_strict
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T21:20:21.016988+00:00
-- url     : https://prove2.me/theorems/938d6ff8-5205-485a-a7ef-5d50fff78069
-- title:
--   Source-sensitive guard counting improves the sensitivity exponent to 2.1308253795
-- statement:
--   Let $s(f)$ and $\operatorname{bs}(f)$ denote the sensitivity and block sensitivity of a finite Boolean function. Set
--
--   $$
--   \alpha=\frac{\log(14055^4)}{\log(61141556)}
--   =2.1308253795064718647\ldots.
--   $$
--
--   For every $\varepsilon>0$ and every integer $S\ge2$, there exist an integer $n$ and a Boolean function $f:\{0,1\}^n\to\{0,1\}$ such that
--
--   $$
--   s(f)\ge S,\qquad \operatorname{bs}(f)\ge s(f)^{\alpha-\varepsilon}.
--   $$
--
--   Furthermore,
--
--   $$
--   \frac{\log(12607^4)}{\log(50063523)}<\alpha.
--   $$
--
--   The new exponent improves the previously proved value by more than $0.000505$. It combines a simultaneous ordinary and source-sensitive labeling with refined guard counting in a coupled recursive Boolean construction. No claim of global optimality is made.
-- source:
--   Strictly improves https://prove2.me/theorems/62961329-4b50-48c7-a1fd-11159da9de26. Refines the coupled Boolean construction https://prove2.me/theorems/13efa201-cabf-4776-8b79-3e67e73e02a0. Attribution to Robin Kothari and the earlier OpenAI sensitivity and local-lemma development is retained in the proof source.

import Mathlib
import Definitions.Def_SensitivityCampaign

theorem SensitivityCampaign.reach_source_61141556_strict : SensitivityCampaign.AchievesExponent
      (Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) ∧
    (Real.log (25260794820729601 : ℝ) / Real.log (50063523 : ℝ) <
      Real.log (39023246726150625 : ℝ) / Real.log (61141556 : ℝ)) := by sorry
