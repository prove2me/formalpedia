-- Prove2me | Theorems.Thm_TitiusBode_doubling_covering
-- name    : TitiusBode.doubling_covering
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:31.872925+00:00
-- url     : https://prove2.me/theorems/00d0c99a-5b68-4364-a0dd-57a0be556e92
-- title:
--   Footnote 1 — any at-most-doubling unbounded sequence covers with a $-25\%/+50\%$ band
-- statement:
--   Let $(p_k)_{k\ge 0}$ be a sequence of real numbers that at most doubles at each step and is unbounded above:
--
--   1. $p_{k+1} \le 2p_k$ for all $k$;
--   2. for every $M \in \mathbb R$ there is $k$ with $p_k \ge M$.
--
--   Then for every real $d \ge \tfrac34 p_0$ there is $k$ with
--
--   $$
--   -\frac14 \;\le\; \frac{d - p_k}{p_k} \;\le\; \frac12 .
--   $$
--
--   This is the general principle behind footnote 1 to the data table of the source ("each Titius–Bode rule distance is approximately twice the preceding value. Hence, an arbitrary planet may be found within $-25\%$ to $+50\%$ of one of the predicted positions"); it applies to any Titius–Bode-type rule whose consecutive ratios do not exceed $2$.
-- source:
--   Wikipedia, "Titius–Bode law", revision oldid=1372822920, https://en.wikipedia.org/w/index.php?title=Titius%E2%80%93Bode_law&oldid=1372822920, section "Data", footnote 1 to the table

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology

namespace TitiusBode
theorem doubling_covering (p : ℕ → ℝ) (hstep : ∀ k, p (k + 1) ≤ 2 * p k)
    (hunbdd : ∀ M : ℝ, ∃ k, M ≤ p k) (d : ℝ) (hd : 3 / 4 * p 0 ≤ d) :
    ∃ k, -1 / 4 ≤ deviation d (p k) ∧ deviation d (p k) ≤ 1 / 2 := by sorry
end TitiusBode
