-- Prove2me | Theorems.Thm_TitiusBode_within_deviation_band
-- name    : TitiusBode.within_deviation_band
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:31:14.624631+00:00
-- url     : https://prove2.me/theorems/6b222948-7d23-4905-83bc-71bbc6226d29
-- title:
--   Every distance $\ge 0.3$ au is within $-25\%$ to $+50\%$ of a Titius–Bode position
-- statement:
--   Let $a(n) = 0.4 + 0.3\cdot 2^n$ (astronomical units) be the Titius–Bode distance, for $n \in \{-\infty, 0, 1, 2, \dots\}$ with $2^{-\infty} = 0$. For every real $d \ge 0.3$ there is an index $n$ such that the relative deviation of $d$ from $a(n)$ lies between $-25\%$ and $+50\%$:
--
--   $$
--   -\frac14 \;\le\; \frac{d - a(n)}{a(n)} \;\le\; \frac12 .
--   $$
--
--   This is the observation recorded in footnote 1 of the data table of the source: since consecutive predicted distances roughly double, an arbitrary planet may be found within $-25\%$ to $+50\%$ of one of the predicted positions. The bound $d \ge 0.3 = \tfrac34\cdot 0.4$ is the range in which the claim holds; for $0 < d < 0.3$ no predicted position is close enough.
--
--   **Formalization Note** The source says "an arbitrary planet" without a range; the explicit hypothesis $d \ge 0.3$ is the exact range of validity.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Data", footnote 1 to the table

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem within_deviation_band (d : ℝ) (hd : 0.3 ≤ d) :
    ∃ n : WithBot ℕ, -0.25 ≤ deviation d (tbAU n) ∧ deviation d (tbAU n) ≤ 0.5 := by sorry
end TitiusBode
