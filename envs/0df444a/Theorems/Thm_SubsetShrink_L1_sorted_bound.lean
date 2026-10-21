-- Prove2me | Theorems.Thm_SubsetShrink_L1_sorted_bound
-- name    : SubsetShrink.L1.sorted_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:31.89955+00:00
-- url     : https://prove2.me/theorems/0541c0d4-7c92-46ba-ad14-28435ee1a175
-- title:
--   p. 43 — sorted-coordinate sum bounded by the ℓ1 norm
-- statement:
--   For $p\ge1$ and $u\in\mathbb R^p$, let $u_j^\sharp$ be the decreasing rearrangement of $|u_j|$. Then
--
--   $$\sum_{j=1}^p u_j^\sharp\sqrt{\log(2p/j)}\le\sqrt{\log(2p)}\,\|u\|_1.$$
--
--   This bounds the sorted-coordinate component of $\mathcal F$ using an ordinary $\ell_1$ norm.
--
--   **Formalization Note** The one-based $j$ is represented by `j.val + 1` in the permutation maximum.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 43, display after first slow-rate proof

import Mathlib
import Definitions.Def_SubsetShrink_L1_Model

namespace SubsetShrink.L1

/-- The sorted-coordinate display in B.6, p. 43. -/
theorem sorted_bound {p : ℕ} (hp : 1 ≤ p) (u : Fin p → ℝ) :
    SubsetShrink.Events.sortedSum u ≤ Real.sqrt (Real.log (2 * (p : ℝ))) * SubsetShrink.Events.l1 u := by sorry

end SubsetShrink.L1
