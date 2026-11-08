-- Prove2me | Theorems.Thm_TightClock_lemma_6_9
-- name    : TightClock.lemma_6_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:28:17.210207+00:00
-- url     : https://prove2.me/theorems/cb7c9705-eb51-4c42-bc16-929a6b9409e1
-- title:
--   Lemma 6.9 — few exceptional nodes
-- statement:
--   For every fixed integer $q\ge8$ and all sufficiently large $L$, the random tree of Instance 11 is good with probability at least $1-2/n^2$.
--
--   Since a good tree has fewer than $n$ exceptional nodes simultaneously at every state, the bound holds even though the auction may adapt to the realized tree.
--
--   Differences from the source:
--   - encoding: probability over the tree → `treeExpect` of an indicator; reason: the tree law is finite
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.9, §6.5, p.43 (PDF p.46)

import Mathlib
import Definitions.Def_TightClock_treeExpect
import Definitions.Def_TightClock_IsGoodTree

set_option autoImplicit false

namespace TightClock

open Classical in
/-- Lemma 6.9 (Few exceptional nodes), p.43 (PDF 46), of Afshinmehr et al., manuscript (STOC 2027 submission): for every
fixed `q ≥ 8` and all sufficiently large `L`, the tree is good with probability at least `1 − 2/n²`. -/
theorem lemma_6_9 (q : ℕ) (hq : 8 ≤ q) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      1 - 2 / ((bidderCount q L : ℝ) ^ 2) ≤ treeExpect q L (fun T => if IsGoodTree T then 1 else 0) := by sorry

end TightClock
