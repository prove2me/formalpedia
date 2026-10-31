-- Prove2me | Theorems.Thm_Underdogs_posterior_FS_gt_SS_iff
-- name    : Underdogs.posterior_FS_gt_SS_iff
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:18.883225+00:00
-- url     : https://prove2.me/theorems/01c44ee1-8c99-491d-82cb-a556d521703d
-- title:
--   Eq. (4): when failure-then-success beats two successes
-- statement:
--   In the two-period model, write $p_h, p_l\in(0,1)$ for the first-period success probabilities and $p_{h,S},p_{l,S},p_{h,F},p_{l,F}\in(0,1]$ for the second-period ones (the standing domain). Then succeeding after an initial failure is stronger evidence of high quality than succeeding twice if and only if
--   $$
--   P(H\mid F,S)>P(H\mid S,S)\iff \frac{1-p_h}{1-p_l}\,\frac{p_{h,F}}{p_{l,F}}>\frac{p_h}{p_l}\,\frac{p_{h,S}}{p_{l,S}}.
--   $$
--
--   The criterion says that $(F,S)$ is more impressive when success after failure is highly diagnostic ($p_{h,F}/p_{l,F}$ large), an initial success is only weakly diagnostic ($p_h/p_l$ small), and success after success is not very diagnostic ($p_{h,S}/p_{l,S}$ small).
--
--   Differences from the source:
--   - encoding: six success probabilities, used as denominators in the formulas → p_h, p_l in (0,1) and p_{h,S}, p_{l,S}, p_{h,F}, p_{l,F} in (0,1] (Params.Standing); reason: excludes exactly the values at which a denominator of the paper's formulas (p_h, p_l, 1 − p_h, 1 − p_l, p_{q,S}, p_{q,F}) vanishes
--   - encoding: Pr(H|·,·) computed by Bayes' rule → the conditional measure μ[|s] of the joint law (prior 1/2) on the event quality = H, as a real via toReal; reason: the definition of a posterior probability; the closed forms are theorems, not definitions
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, eq. (4), p.8 (PDF p.9); proved as eq. (10), Appendix A, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh

namespace Underdogs

/-- Eq. (4): in the two-period model with its six success probabilities in the
standing domain (`Params.Standing`),
`P(H|F,S) > P(H|S,S)` if and only if
`(1 − p_h)/(1 − p_l) · p_{h,F}/p_{l,F} > p_h/p_l · p_{h,S}/p_{l,S}`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §4, eq. (4), p.8 (PDF p.9); proved as eq. (10), Appendix A, p.35 (PDF p.36).

**Formalization Note** `P(H|F,S)` and `P(H|S,S)` are `P.posteriorHigh false true` and
`P.posteriorHigh true true`. -/
theorem posterior_FS_gt_SS_iff (P : Params) (hP : P.Standing) :
    P.posteriorHigh false true > P.posteriorHigh true true ↔
      (1 - P.ph) / (1 - P.pl) * (P.phF / P.plF) > P.ph / P.pl * (P.phS / P.plS) := by sorry

end Underdogs
