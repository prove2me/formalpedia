-- Prove2me | Theorems.Thm_Underdogs_posterior_SS_eq
-- name    : Underdogs.posterior_SS_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:25.891367+00:00
-- url     : https://prove2.me/theorems/3947f1bb-0b31-4c7e-ae29-5898d75e4e2b
-- title:
--   Posterior of high quality after two successes (Appendix A)
-- statement:
--   In the two-period model, let $P(H\mid S,S)$ be the posterior probability that an agent who succeeds twice is of high quality. Write $p_h, p_l\in(0,1)$ for the first-period success probabilities and $p_{h,S},p_{l,S},p_{h,F},p_{l,F}\in(0,1]$ for the second-period ones (the standing domain). Then
--   $$
--   P(H\mid S,S)=\frac{p_{h,S}p_h\,0.5}{p_{h,S}p_h\,0.5+p_{l,S}p_l\,0.5}=\frac{1}{1+\dfrac{p_{l,S}p_l}{p_{h,S}p_h}}.
--   $$
--
--   Together with the formula for $P(H\mid F,S)$ it reduces the comparison of the two track records to an inequality between the six parameters.
--
--   Differences from the source:
--   - encoding: six success probabilities, used as denominators in the formulas → p_h, p_l in (0,1) and p_{h,S}, p_{l,S}, p_{h,F}, p_{l,F} in (0,1] (Params.Standing); reason: excludes exactly the values at which a denominator of the paper's formulas (p_h, p_l, 1 − p_h, 1 − p_l, p_{q,S}, p_{q,F}) vanishes
--   - encoding: Pr(H|·,·) computed by Bayes' rule → the conditional measure μ[|s] of the joint law (prior 1/2) on the event quality = H, as a real via toReal; reason: the definition of a posterior probability; the closed forms are theorems, not definitions
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix A, display for Pr(H|S,S), p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh

namespace Underdogs

/-- Appendix A, posterior after two successes: in the two-period model with its six success
probabilities in the standing domain (`Params.Standing`),
`Pr(H|S,S) = p_{h,S} p_h 0.5 / (p_{h,S} p_h 0.5 + p_{l,S} p_l 0.5) = 1 / (1 + p_{l,S} p_l / (p_{h,S} p_h))`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix A, display for Pr(H|S,S), p.35 (PDF p.36).

**Formalization Note** `Pr(H|S,S)` is `P.posteriorHigh true true`, the conditional probability
under the joint law. -/
theorem posterior_SS_eq (P : Params) (hP : P.Standing) :
    P.posteriorHigh true true =
        P.phS * P.ph * 0.5 / (P.phS * P.ph * 0.5 + P.plS * P.pl * 0.5) ∧
      P.posteriorHigh true true = 1 / (1 + P.plS * P.pl / (P.phS * P.ph)) := by sorry

end Underdogs
