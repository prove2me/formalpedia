-- Prove2me | Theorems.Thm_TightClock_lemma_6_6
-- name    : TightClock.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:20:09.198763+00:00
-- url     : https://prove2.me/theorems/6a421ca3-5109-4ba7-ad69-8eab9af28c70
-- title:
--   Lemma 6.6 — price-test stability
-- statement:
--   For every fixed node $S$ of a realized tree, every single-step clock and every step $t$,
--
--   $$\mathbb E[A_S(J^{t+1})\mid H^t]\le A_S(J^t).$$
--
--   Thus an auction cannot increase the expected account of a fixed node by learning more about bidders.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: a clock auction after the §6.2 reduction, with tree and seed part of $H^t$ → a valid deterministic `SingleStepStrategy`, with tree and seed fixed parameters; reason: the seed and the tree are fixed before the conditioning, as in the proof of Proposition 6.11; the prior is independent of both
--   - encoding: $\mathbb E[\cdot\mid H^t]$ → `condExpect`, the ratio of two finite sums, at a history $h$ of positive probability; reason: the law is finite, and a history of probability zero is not conditioned on
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.6, §6.4, p.41 (PDF p.44)

import Mathlib
import Definitions.Def_TightClock_account
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsValidSingleStep
import Definitions.Def_TightClock_condExpect

set_option autoImplicit false

namespace TightClock

/-- Lemma 6.6 (Price-test stability), p.41 (PDF 44), of Afshinmehr et al., manuscript (STOC 2027 submission): for every
fixed node `S` and every step `t`, `E[A_S(Jᵗ⁺¹) | Hᵗ] ≤ A_S(Jᵗ)`. -/
theorem lemma_6_6 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L) (S : TreeNode q L)
    (σ : SingleStepStrategy (bidderCount q L)) (hσ : IsValidSingleStep q L (familyOf T) σ)
    (h : SingleStepHistory (bidderCount q L))
    (hh : 0 < histProb q L (hardPrior q L hq hL) σ h) :
    condExpect q L (hardPrior q L hq hL) σ h
        (fun v => account T S (stateOf q L (ssHist q L σ v (h.length + 1)))) ≤
      account T S (stateOf q L h) := by sorry

end TightClock
