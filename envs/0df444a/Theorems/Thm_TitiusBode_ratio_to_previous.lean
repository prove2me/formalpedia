-- Prove2me | Theorems.Thm_TitiusBode_ratio_to_previous
-- name    : TitiusBode.ratio_to_previous
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:03.750204+00:00
-- url     : https://prove2.me/theorems/83b47605-ddb6-4af7-9d31-4253b617efa1
-- title:
--   Footnote 1 — consecutive distances less than double, ratio tending to $2$
-- statement:
--   Let $a(n) = 0.4 + 0.3\cdot 2^n$ for $n \in \{-\infty, 0, 1, \dots\}$ and $a_n$ the same expression for $n \in \mathbb N$. Then
--
--   1. $a(0) < 2\,a(-\infty)$, i.e. $0.7 < 0.8$;
--   2. $a_{n+1} < 2a_n$ for every $n \in \mathbb N$;
--   3. $\displaystyle \lim_{n\to\infty} \frac{a_{n+1}}{a_n} = 2$.
--
--   This is the first sentence of footnote 1 to the data table of the source: for large $k$ each Titius–Bode distance is approximately twice the preceding value, while for small $k$ the predicted distances do not fully double.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Data", footnote 1 to the table

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem ratio_to_previous :
    tbAU ((0 : ℕ) : WithBot ℕ) < 2 * tbAU ⊥ ∧
    (∀ n : ℕ, tbCanonical (n + 1) < 2 * tbCanonical n) ∧
    Tendsto (fun n : ℕ => tbCanonical (n + 1) / tbCanonical n) atTop (𝓝 2) := by sorry
end TitiusBode
