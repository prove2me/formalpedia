-- Prove2me | Theorems.Thm_SubsetShrink_Events_eq_28
-- name    : SubsetShrink.Events.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T19:31:31.078548+00:00
-- url     : https://prove2.me/theorems/10d1f6f2-0f54-455e-b5f7-d20708bc6708
-- title:
--   (28), p. 38 — ∑_j u♯_j √log(2p/j) ≤ ‖u‖ √(∑_{j≤s} log(2p/j)) ≤ √(s log(2ep/s)) ‖u‖ for u ∈ B₀(s)
-- statement:
--   Let $1\le s\le p$ and let $u\in\mathbb R^p$ satisfy $\|u\|_0\le s$. Write $u^\sharp_1\ge\dots\ge u^\sharp_p$ for the non-increasing rearrangement of $|u_1|,\dots,|u_p|$. Then
--   $$\sum_{j=1}^{p}u^\sharp_j\sqrt{\log(2p/j)}\le\|u\|\sqrt{\sum_{j=1}^{s}\log(2p/j)}\le\sqrt{s\log(2ep/s)}\,\|u\|.$$
--
--   This bounds the sorted-$\ell_1$ entry of the event $\mathcal F$ by the threshold of $\mathcal E_s$ for $s$-sparse vectors, the second ingredient of the inclusion $\mathcal F\subseteq\mathcal E_s$.
--
--   **Formalization Note** The left side is the definition `sortedSum`: the maximum over permutations $\pi$ of $\sum_j|u_{\pi(j)}|\sqrt{\log(2p/j)}$, equal to the sorted sum by the rearrangement inequality (the weights are non-increasing and non-negative). Indices of `Fin p` are 0-based.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 38, proof of Theorem 1 (B.1), (28)

import Mathlib
import Definitions.Def_SubsetShrink_Events_Model

open MeasureTheory ProbabilityTheory

namespace SubsetShrink.Events
theorem eq_28 {p s : ℕ} (hs : 1 ≤ s) (hsp : s ≤ p) (u : Fin p → ℝ) (hu : l0 u ≤ s) :
    sortedSum u ≤ l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)) ∧
      l2 u * Real.sqrt (∑ j ∈ Finset.Icc 1 s, Real.log (2 * (p : ℝ) / j)) ≤
        Real.sqrt ((s : ℝ) * Real.log (2 * Real.exp 1 * p / s)) * l2 u := by sorry
end SubsetShrink.Events
