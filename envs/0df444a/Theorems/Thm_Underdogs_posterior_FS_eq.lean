-- Prove2me | Theorems.Thm_Underdogs_posterior_FS_eq
-- name    : Underdogs.posterior_FS_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:25.037319+00:00
-- url     : https://prove2.me/theorems/a849927e-89e2-4624-8e10-c1c62ef75984
-- title:
--   Posterior of high quality after failure then success (Appendix A)
-- statement:
--   In the two-period model, let $P(H\mid F,S)$ be the posterior probability that an agent who first fails and then succeeds is of high quality. Write $p_h, p_l\in(0,1)$ for the first-period success probabilities and $p_{h,S},p_{l,S},p_{h,F},p_{l,F}\in(0,1]$ for the second-period ones (the standing domain). Then, by Bayes' rule,
--   $$
--   P(H\mid F,S)=\frac{p_{h,F}(1-p_h)\,0.5}{p_{h,F}(1-p_h)\,0.5+p_{l,F}(1-p_l)\,0.5}=\frac{1}{1+\dfrac{p_{l,F}(1-p_l)}{p_{h,F}(1-p_h)}}.
--   $$
--
--   This is the first ingredient of the comparison between the "underdog" track record $(F,S)$ and the double success $(S,S)$.
--
--   Differences from the source:
--   - encoding: six success probabilities, used as denominators in the formulas → p_h, p_l in (0,1) and p_{h,S}, p_{l,S}, p_{h,F}, p_{l,F} in (0,1] (Params.Standing); reason: excludes exactly the values at which a denominator of the paper's formulas (p_h, p_l, 1 − p_h, 1 − p_l, p_{q,S}, p_{q,F}) vanishes
--   - encoding: Pr(H|·,·) computed by Bayes' rule → the conditional measure μ[|s] of the joint law (prior 1/2) on the event quality = H, as a real via toReal; reason: the definition of a posterior probability; the closed forms are theorems, not definitions
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix A, display for Pr(H|F,S), p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh

namespace Underdogs

/-- Appendix A, posterior after a failure followed by a success: in the two-period model with its
six success probabilities in the standing domain (`Params.Standing`),
`Pr(H|F,S) = p_{h,F}(1 − p_h)0.5 / (p_{h,F}(1 − p_h)0.5 + p_{l,F}(1 − p_l)0.5)
            = 1 / (1 + p_{l,F}(1 − p_l) / (p_{h,F}(1 − p_h)))`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix A, display for Pr(H|F,S), p.35 (PDF p.36).

**Formalization Note** `Pr(H|F,S)` is `P.posteriorHigh false true`, the conditional probability
under the joint law (failure first, then success). -/
theorem posterior_FS_eq (P : Params) (hP : P.Standing) :
    P.posteriorHigh false true =
        P.phF * (1 - P.ph) * 0.5 / (P.phF * (1 - P.ph) * 0.5 + P.plF * (1 - P.pl) * 0.5) ∧
      P.posteriorHigh false true = 1 / (1 + P.plF * (1 - P.pl) / (P.phF * (1 - P.ph))) := by sorry

end Underdogs
