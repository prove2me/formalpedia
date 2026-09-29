-- Prove2me | Theorems.Thm_Pade_pade_exp_five_five
-- name    : Pade.pade_exp_five_five
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:57:55.692369+00:00
-- url     : https://prove2.me/theorems/e07f0646-0d00-4fb9-81dc-ee1aaeb430f3
-- title:
--   $[5/5]$ Padé approximant of $\exp(x)$
-- statement:
--   **The $[5/5]$ Padé approximant of $\exp(x)$.** Let $E(x) = \sum_{k\ge0} x^k/k! \in \mathbb{Q}[[x]]$ be the formal exponential series, and set
--
--   $$ P(x) = 1 + \tfrac{1}{2}x + \tfrac{1}{9}x^2 + \tfrac{1}{72}x^3 + \tfrac{1}{1008}x^4 + \tfrac{1}{30240}x^5, \qquad Q(x) = P(-x). $$
--
--   Then $(P,Q)$ is a Padé pair of type $[5/5]$ for $E$: both degrees are at most $5$, $Q \ne 0$, and
--
--   $$ Q(x)E(x) - P(x) \equiv 0 \pmod{x^{11}} . $$
--
--   Equivalently,
--
--   $$ \exp(x) \;\approx\; \frac{1 + \frac{1}{2}x + \frac{1}{9}x^2 + \frac{1}{72}x^3 + \frac{1}{1008}x^4 + \frac{1}{30240}x^5}{1 - \frac{1}{2}x + \frac{1}{9}x^2 - \frac{1}{72}x^3 + \frac{1}{1008}x^4 - \frac{1}{30240}x^5}, $$
--
--   with agreement of the Maclaurin expansions through order $10 = m+n$. This is the second worked example of the source's *Examples* section. The antisymmetry $Q(x) = P(-x)$ is the diagonal symmetry of the Padé table for $\exp$, reflecting $\exp(-x) = 1/\exp(x)$; the example is a demanding test vector, since eleven rational coefficient identities must hold simultaneously.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Examples', subsection 'exp(x)'

import Mathlib
import Definitions.Def_pade_approximant_def
open Polynomial

namespace Pade

theorem pade_exp_five_five :
    IsPadeApproximant (PowerSeries.exp ℚ) 5 5
      (1 + C (1 / 2 : ℚ) * X + C (1 / 9 : ℚ) * X ^ 2 + C (1 / 72 : ℚ) * X ^ 3
        + C (1 / 1008 : ℚ) * X ^ 4 + C (1 / 30240 : ℚ) * X ^ 5)
      (1 - C (1 / 2 : ℚ) * X + C (1 / 9 : ℚ) * X ^ 2 - C (1 / 72 : ℚ) * X ^ 3
        + C (1 / 1008 : ℚ) * X ^ 4 - C (1 / 30240 : ℚ) * X ^ 5) := by sorry

end Pade
