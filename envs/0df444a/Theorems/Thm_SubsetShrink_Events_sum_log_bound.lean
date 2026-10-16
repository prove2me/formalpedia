-- Prove2me | Theorems.Thm_SubsetShrink_Events_sum_log_bound
-- name    : SubsetShrink.Events.sum_log_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:22.3177+00:00
-- url     : https://prove2.me/theorems/e4bc9c9a-3131-429d-ba34-413b27ca2aa2
-- title:
--   p. 38, display after (27) — ∑_{j≤s} log(2p/j) = s log(2p) − log(s!) ≤ s log(2ep/s)
-- statement:
--   Let $1\le s\le p$ be integers. Then
--   $$\sum_{j=1}^{s}\log(2p/j) = s\log(2p)-\log(s!)\le s\log(2ep/s).$$
--
--   The inequality is the bound $\log(s!)\ge s\log(s/e)$ rewritten; it controls the sum of the squared weights $\log(2p/j)$ of the sorted-$\ell_1$ term over the first $s$ indices, which enters the proof of Theorem 1 through (28).
--
--   **Formalization Note** The sum runs over $j\in\{1,\dots,s\}$ (`Finset.Icc 1 s`) with natural logarithms; $p\ge s\ge1$ keeps every logarithm's argument positive.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 38, proof of Theorem 1 (B.1), display after (27)

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem sum_log_bound {p s : ℕ} (hs : 1 ≤ s) (hsp : s ≤ p) :
    ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j) =
        (s : ℝ) * Real.log (2 * p) - Real.log (s.factorial) ∧
      ∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j) ≤
        (s : ℝ) * Real.log (2 * Real.exp 1 * p / s) := by sorry
end SubsetShrink.Events
