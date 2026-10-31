-- Prove2me | Theorems.Thm_Underdogs_condition_6_necessary_not_sufficient
-- name    : Underdogs.condition_6_necessary_not_sufficient
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:57.361807+00:00
-- url     : https://prove2.me/theorems/0860d5f0-349b-4b0e-b49d-5443a3f28006
-- title:
--   Condition (6) is necessary but not sufficient for $P(H\mid F,S)>P(H\mid S,S)$
-- statement:
--   Let $g(q,r)$ be the probability of success of an agent of quality $q$ with resources $r$; the low and high quality levels are $l$ and $h$. Agents start with resources $r_2$, a first-period success raises them to $r_3$ and a failure lowers them to $r_1$. Write $P(H\mid F,S)$ and $P(H\mid S,S)$ for the posterior probabilities of high quality (prior $1/2$) after failure-then-success and after two successes. **Condition (6)**, at $r=r_1$ and $r+\delta=r_3$, is
--   $$
--   \frac{g(l,r_3)-g(l,r_1)}{g(l,r_1)}>\frac{g(h,r_3)-g(h,r_1)}{g(h,r_1)}.
--   $$
--
--   1. **Necessity.** For all $g,l,h,r_1,r_2,r_3$ with $g(l,r_2),g(h,r_2)\in(0,1)$, $g(q,r_1),g(q,r_3)\in(0,1]$ for $q\in\{l,h\}$, and $g(l,r_2)\le g(h,r_2)$:
--   $$
--   P(H\mid F,S)>P(H\mid S,S)\implies\text{condition (6)}.
--   $$
--   2. **Non-sufficiency.** There exist $l<h$, $r_1<r_2<r_3$ and a function $g:\mathbb R^2\to(0,1)$, strictly increasing in quality and in resources, such that condition (6) holds and yet $P(H\mid F,S)\le P(H\mid S,S)$.
--
--   This is the paper's answer to when "overcoming adversity" can be impressive: only when low-quality agents benefit proportionally more from resources, and even then not always, because the effect must be strong enough to compensate for the initial success.
--
--   **Formalization Note** Condition (6) is the definition `Condition6 g l h r1 (r3 - r1)`. The posteriors are conditional probabilities under the joint law, not closed-form expressions.
--
--   Differences from the source:
--   - reading: condition (6) with unspecified r and δ → (6) at r = r1, r + δ = r3 (δ = r3 − r1); reason: Appendix B's necessary condition g(l,r3)/g(l,r1) > g(h,r3)/g(h,r1) is (6) rearranged at exactly this pair; reading (6) for all r, δ would make necessity false
--   - generalization: necessity under l < h, r1 < r2 < r3, g increasing in quality and resources → necessity under g(l, r2) ≤ g(h, r2) only; reason: the argument uses only the comparison of first-period success probabilities, which the paper's assumptions imply (also under weak monotonicity); the paper's clause is an instance
--   - reading: "not sufficient" → an explicit model satisfying all standing assumptions of §5.1, with g strictly increasing in each argument and valued in (0,1), where (6) holds and P(H|F,S) ≤ P(H|S,S); reason: non-sufficiency means a counterexample within the paper's setting; the strict reading of "increasing" makes the witness satisfy the weak reading too
--   - encoding: g(q, r) a success probability → in clause 1: g(q, r2) in (0,1), g(q, r1) and g(q, r3) in (0,1] for q ∈ {l, h}; reason: excludes exactly the values at which a denominator of (6) or (12) vanishes
--   - encoding: Pr(H|·,·) computed by Bayes' rule → the conditional measure μ[|s] of the joint law (prior 1/2) on the event quality = H, as a real via toReal; reason: the definition of a posterior probability; the closed forms are theorems, not definitions
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, p.11 (PDF p.12): "Condition (6) is a necessary but not sufficient condition for P(H|F, S) > P(H|S, S) (see Appendix B)."; proof of necessity in Appendix B, p.35 (PDF p.36): "Because g(h, r2) > g(l, r2) implies that g(h, r2)/(1 − g(h, r2)) is larger than g(l, r2)/(1 − g(l, r2)), 12 is only satisfied if g(l,r3)/g(h,r3) > g(l,r1)/g(h,r1), i.e., if g(l,r3)/g(l,r1) > g(h,r3)/g(h,r1), which is thus a necessary condition for Pr(H|F, S) > Pr(H|S, S)."

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh
import Definitions.Def_Underdogs_ofResource
import Definitions.Def_Underdogs_Condition6

namespace Underdogs

/-- Condition (6) is a necessary but not sufficient condition for `P(H|F,S) > P(H|S,S)`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, §5.1, p.11 (PDF p.12), with the proof of necessity in Appendix B, p.35 (PDF p.36).

The success probability is a function `g(q, r)` of quality and resources; agents start with
resources `r2`, a first-period success raises them to `r3` and a failure lowers them to `r1`
(`ofResource`). Condition (6) is taken at `r = r1`, `r + δ = r3`.

1. *Necessity.* For every `g`, `l`, `h`, `r1`, `r2`, `r3` such that the induced model is in
   its standing domain (`g(q, r2)` in (0,1), `g(q, r1)` and `g(q, r3)` in (0,1], for `q ∈ {l, h}`)
   and `g(l, r2) ≤ g(h, r2)`:
   if `P(H|F,S) > P(H|S,S)`, then condition (6) holds at `(r1, r3 − r1)`.
2. *Non-sufficiency.* There are `g`, `l < h`, `r1 < r2 < r3`, with `g` valued in (0,1) and
   strictly increasing in each argument, such that condition (6) holds at `(r1, r3 − r1)` but
   `P(H|F,S) > P(H|S,S)` fails.

**Formalization Note** In clause 1 the paper's `l < h`, `r1 < r2 < r3` and monotonicity of `g` are
replaced by the only consequence the argument uses, `g(l, r2) ≤ g(h, r2)`, so clause 1 contains
the paper's statement. Clause 2's witness satisfies every standing assumption of §5.1, with
"increasing" in its strict reading (which implies the weak one). -/
theorem condition_6_necessary_not_sufficient :
    (∀ (g : ℝ → ℝ → ℝ) (l h r1 r2 r3 : ℝ),
        (ofResource g l h r1 r2 r3).Standing → g l r2 ≤ g h r2 →
        (ofResource g l h r1 r2 r3).posteriorHigh false true >
          (ofResource g l h r1 r2 r3).posteriorHigh true true →
        Condition6 g l h r1 (r3 - r1)) ∧
    (∃ (g : ℝ → ℝ → ℝ) (l h r1 r2 r3 : ℝ),
        l < h ∧ r1 < r2 ∧ r2 < r3 ∧
        (∀ q r, 0 < g q r ∧ g q r < 1) ∧
        (∀ r, StrictMono fun q => g q r) ∧ (∀ q, StrictMono (g q)) ∧
        Condition6 g l h r1 (r3 - r1) ∧
        ¬ ((ofResource g l h r1 r2 r3).posteriorHigh false true >
            (ofResource g l h r1 r2 r3).posteriorHigh true true)) := by sorry

end Underdogs
