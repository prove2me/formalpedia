-- Prove2me | Theorems.Thm_Underdogs_eq12_resource_criterion
-- name    : Underdogs.eq12_resource_criterion
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:53:40.013991+00:00
-- url     : https://prove2.me/theorems/a64cd639-2ecb-4f73-9064-dc7679aaa24c
-- title:
--   Eq. (12): the criterion in terms of the success function $g(q,r)$
-- statement:
--   Let $g(q,r)$ be the success probability of quality $q$ with resources $r$, with low and high quality levels $l,h$. Agents start with resources $r_2$; success raises them to $r_3$ and failure lowers them to $r_1$, so $p_h=g(h,r_2)$, $p_{h,S}=g(h,r_3)$, $p_{h,F}=g(h,r_1)$ and likewise for $l$. Assume $g(l,r_2),g(h,r_2)\in(0,1)$ and $g(q,r_1),g(q,r_3)\in(0,1]$ for $q\in\{l,h\}$. Then
--   $$
--   P(H\mid F,S)>P(H\mid S,S)\iff\frac{g(l,r_1)}{g(h,r_1)}\,\frac{1-g(l,r_2)}{1-g(h,r_2)}<\frac{g(l,r_3)}{g(h,r_3)}\,\frac{g(l,r_2)}{g(h,r_2)},
--   $$
--   and the right-hand inequality is equivalent to
--   $$
--   \frac{g(h,r_2)}{1-g(h,r_2)}\,\frac{g(l,r_1)}{g(h,r_1)}<\frac{g(l,r_2)}{1-g(l,r_2)}\,\frac{g(l,r_3)}{g(h,r_3)}.
--   $$
--
--   The second form separates the first-period odds from the ratios of success probabilities after failure and after success, which is what the necessity argument of Appendix B uses.
--
--   Differences from the source:
--   - reading: (12) printed as "Pr(H|F,S) is larger than Pr(H|S,S) whenever A ⟹ B" → Pr(H|F,S) > Pr(H|S,S) ↔ A, and A ↔ B; reason: (12) is the first inequality of (10) with the resource model substituted, and the body states the underlying criterion (4) as "if and only if"; the arrow is an algebraic rearrangement by positive factors
--   - generalization: failure decreases resources from r2 to r1 < r2, success increases them to r3 > r2 → no ordering assumed on r1, r2, r3 (or on l, h); reason: the equivalences are a substitution and a rearrangement and do not use the orderings; the paper's case is an instance
--   - encoding: g(q, r) a success probability → g(q, r2) in (0,1), g(q, r1) and g(q, r3) in (0,1] for q ∈ {l, h}; reason: the standing domain of the induced model; excludes exactly the values at which a denominator of (12) vanishes
--   - encoding: Pr(H|·,·) computed by Bayes' rule → the conditional measure μ[|s] of the joint law (prior 1/2) on the event quality = H, as a real via toReal; reason: the definition of a posterior probability; the closed forms are theorems, not definitions
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix B, eq. (12), p.35 (PDF p.36)

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh
import Definitions.Def_Underdogs_ofResource

namespace Underdogs

/-- Eq. (12), Appendix B: in the two-period model induced by a success-probability function
`g(q, r)` (first period at resources `r2`, second period at `r3` after a success and at `r1`
after a failure), with `g(l, r2)`, `g(h, r2)` in (0,1) and `g(q, r1)`, `g(q, r3)` in (0,1] for
`q ∈ {l, h}` (the standing domain of the induced model):
`Pr(H|F,S) > Pr(H|S,S)` if and only if
`g(l,r1)/g(h,r1) · (1 − g(l,r2))/(1 − g(h,r2)) < g(l,r3)/g(h,r3) · g(l,r2)/g(h,r2)`,
and this first inequality is equivalent to the second,
`g(h,r2)/(1 − g(h,r2)) · g(l,r1)/g(h,r1) < g(l,r2)/(1 − g(l,r2)) · g(l,r3)/g(h,r3)`.
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix B, eq. (12), p.35 (PDF p.36).

**Formalization Note** The page's "whenever … ⟹" is read as two equivalences: (12) is the first
inequality of (10) with the parameters of the resource model substituted, and the body states the
underlying criterion (4) as an "if and only if". The orderings `r1 < r2 < r3` and `l < h` are
not needed for this rewriting and are not assumed. -/
theorem eq12_resource_criterion (g : ℝ → ℝ → ℝ) (l h r1 r2 r3 : ℝ)
    (hP : (ofResource g l h r1 r2 r3).Standing) :
    ((ofResource g l h r1 r2 r3).posteriorHigh false true >
        (ofResource g l h r1 r2 r3).posteriorHigh true true ↔
      g l r1 / g h r1 * ((1 - g l r2) / (1 - g h r2)) < g l r3 / g h r3 * (g l r2 / g h r2)) ∧
    (g l r1 / g h r1 * ((1 - g l r2) / (1 - g h r2)) < g l r3 / g h r3 * (g l r2 / g h r2) ↔
      g h r2 / (1 - g h r2) * (g l r1 / g h r1) < g l r2 / (1 - g l r2) * (g l r3 / g h r3)) := by sorry

end Underdogs
