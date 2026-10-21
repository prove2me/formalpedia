-- Prove2me | Theorems.Thm_SensitivityCampaign_reach_source_q5_best_3738277295413674
-- name    : SensitivityCampaign.reach_source_q5_best_3738277295413674
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-20T23:06:23.656492+00:00
-- url     : https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2
-- title:
--   Separation exponent at least $2.1308255793978239\ldots$
-- statement:
--   Set
--
--   $$\alpha=\frac{\log(1522813785050025472152230187890625)}{\log(3738277295413674)}=\frac{\log(14055^8)}{\log(3738277295413674)}=2.1308255793978239476\ldots.$$
--
--   For every real $\varepsilon>0$ and every natural number $S\ge2$, there exist a natural number $n$ and a total Boolean function $f:\{0,1\}^n\to\{0,1\}$ with
--
--   $$s(f)\ge S,\qquad \operatorname{bs}(f)\ge s(f)^{\alpha-\varepsilon}.$$
--
--   Here $s(f)$ is the maximum number of sensitive singleton coordinates over all inputs, and $\operatorname{bs}(f)$ is the maximum number of pairwise disjoint nonempty sensitive blocks over all inputs. This is the campaign's unchanged `AchievesExponent` predicate at the exact logarithmic value. The decimal is an approximation. The already accepted primitive theorem proves the same quantified assertion and a strict comparison with the preceding five-tolerance bound.
-- source:
--   Exact campaign-template form of https://prove2.me/theorems/01bb63ef-ced2-4ae9-8b81-b5ed295526c6, accepted submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a. Shared definitions and template from https://prove2.me/campaigns/block-sensitivity-vs-sensitivity. Earlier OpenAI and Robin Kothari/Codex attribution is retained in the accepted source. New construction: yousofy with Codex.

import Mathlib
import Definitions.Def_SensitivityCampaign
import Theorems.Thm_SensitivityCampaign_finite_certificate
import Theorems.Thm_SensitivityCampaign_finite_certificate_log
open OAI.Paper320

theorem SensitivityCampaign.reach_source_q5_best_3738277295413674 :
    SensitivityCampaign.AchievesExponent (Real.log (1522813785050025472152230187890625 : ℝ) / Real.log (3738277295413674 : ℝ)) := by sorry
