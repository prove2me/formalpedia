-- Prove2me | Theorems.Thm_Pade_pade_log_one_plus_two_two
-- name    : Pade.pade_log_one_plus_two_two
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T10:57:35.446815+00:00
-- url     : https://prove2.me/theorems/a8120fa6-94b2-40d8-82fa-1598ae805304
-- title:
--   $[2/2]$ Padé approximant of $\ln(1+x)$
-- statement:
--   **The $[2/2]$ Padé approximant of $\ln(1+x)$.** Let $L(x) = x - x^2/2 + x^3/3 - \cdots \in \mathbb{Q}[[x]]$ be the formal logarithmic series. Then the pair
--
--   $$ P(x) = x + \tfrac{1}{2}x^2, \qquad Q(x) = 1 + x + \tfrac{1}{6}x^2 $$
--
--   is a Padé pair of type $[2/2]$ for $L$: both degrees are at most $2$, $Q \ne 0$, and
--
--   $$ Q(x)L(x) - P(x) \equiv 0 \pmod{x^{5}} . $$
--
--   Equivalently, since $Q(0) = 1$,
--
--   $$ \ln(1+x) \;\approx\; \frac{x + \frac{1}{2}x^2}{1 + x + \frac{1}{6}x^2} $$
--
--   with agreement of the Maclaurin expansions through order $4 = m+n$. This is the worked example given in the source's *Examples* section, and it serves as a concrete test vector for the Padé predicate: it pins down the indexing convention (agreement to order $m+n$, not $m+n+1$) on data where every coefficient can be checked by hand.
-- source:
--   Padé approximant, Wikipedia, revision oldid=1374746248, https://en.wikipedia.org/w/index.php?title=Pad%C3%A9_approximant&oldid=1374746248, section 'Examples', subsection 'ln(1+x)'

import Mathlib
import Definitions.Def_pade_approximant_def
import Definitions.Def_log_one_plus_series
open Polynomial

namespace Pade

theorem pade_log_one_plus_two_two :
    IsPadeApproximant logOnePlus 2 2 (X + C (1 / 2 : ℚ) * X ^ 2)
      (1 + X + C (1 / 6 : ℚ) * X ^ 2) := by sorry

end Pade
