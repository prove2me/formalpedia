-- Prove2me | Theorems.Thm_Underdogs_odds_lt_odds
-- name    : Underdogs.odds_lt_odds
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:49:57.440536+00:00
-- url     : https://prove2.me/theorems/cde6dd89-c08f-4887-bae0-cab4d6f535b9
-- title:
--   Odds $x/(1-x)$ are strictly increasing (Appendix B)
-- statement:
--   For real numbers $y<x<1$,
--   $$
--   \frac{y}{1-y}<\frac{x}{1-x}.
--   $$
--
--   In Appendix B this is applied with $x=g(h,r_2)$ and $y=g(l,r_2)$: a high-quality agent's larger first-period success probability gives larger first-period odds, which is the step that turns eq. (12) into the necessary condition (6).
--
--   Differences from the source:
--   - generalization: x = g(h, r2) > y = g(l, r2), both probabilities in (0,1) → any reals y < x < 1; reason: the odds map t ↦ t/(1 − t) is strictly increasing on (−∞, 1); the page's case is an instance
-- source:
--   Denrell, Liu, Maslach, Underdogs and One-Hit Wonders, Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix B, p.35 (PDF p.36)

import Mathlib

namespace Underdogs

/-- The odds step of Appendix B: the odds `x/(1 − x)` are strictly increasing below 1, so for
reals `y < x < 1`, `y/(1 − y) < x/(1 − x)`. On the page, `x = g(h, r2)` and `y = g(l, r2)`:
"g(h, r2) > g(l, r2) implies that g(h, r2)/(1 − g(h, r2)) is larger than g(l, r2)/(1 − g(l, r2))".
Denrell, Liu, Maslach, *Underdogs and One-Hit Wonders: When Is Overcoming Adversity Impressive?*,
Author's Accepted Manuscript (WRAP 165519, May 17, 2022), doi:10.1287/mnsc.2022.4630, Appendix B, p.35 (PDF p.36).

**Formalization Note** Stated for all reals `y < x < 1`, which contains the page's case of two
probabilities in (0,1). -/
theorem odds_lt_odds (x y : ℝ) (hyx : y < x) (hx : x < 1) :
    y / (1 - y) < x / (1 - x) := by sorry

end Underdogs
