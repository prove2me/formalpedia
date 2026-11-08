-- Prove2me | Theorems.Thm_TightClock_coin_law
-- name    : TightClock.coin_law
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:19:24.652214+00:00
-- url     : https://prove2.me/theorems/6d81dc01-c0cc-41b8-a6f4-7fd79f959b32
-- title:
--   §6.2 and (6.6) — the conditional coin law
-- statement:
--   Run a valid single-step clock on the instance, with tree and seed fixed, under the prior $D$. Let $h$ be a history of positive probability, with state $J$. Then:
--
--   1. if the clock's next move at $h$ is a test of bidder $i$, the offer is accepted with conditional probability exactly $\rho$;
--   2. if bidder $i$ is active with cutoff $J_i=j$, then
--
--   $$\mathbb E[X_i\mid H^t=h]\le\frac{y_j}{1-a}.\tag{6.6}$$
--
--   These two facts justify the phrase "price tests are coin tosses": they turn the accounts' two-point computations into statements on the auction.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: a clock auction after the §6.2 reduction, with tree and seed part of $H^t$ → a valid deterministic `SingleStepStrategy`, with tree and seed fixed parameters; reason: the seed and the tree are fixed before the conditioning, as in the proof of Proposition 6.11; the prior is independent of both
--   - encoding: $\mathbb E[\cdot\mid H^t]$ → `condExpect`, the ratio of two finite sums, at a history $h$ of positive probability; reason: the law is finite, and a history of probability zero is not conditioned on
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), §6.2, p.36 (PDF p.39), eq. (6.6)

import Mathlib
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsValidSingleStep
import Definitions.Def_TightClock_condExpect

set_option autoImplicit false

namespace TightClock

open Classical in
/-- §6.2, p.36 (PDF 39), of Afshinmehr et al., manuscript (STOC 2027 submission): "conditional on Hᵗ, the offer is
accepted with probability exactly ρ", and the display (6.6), `E[Xᵢ | Hᵗ] ≤ y_j / (1 − a)` for an active bidder with
`Jᵗᵢ = j`. -/
theorem coin_law (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L)
    (σ : SingleStepStrategy (bidderCount q L)) (hσ : IsValidSingleStep q L (familyOf T) σ)
    (h : SingleStepHistory (bidderCount q L))
    (hh : 0 < histProb q L (hardPrior q L hq hL) σ h) :
    (∀ i, σ h = .test i →
      condExpect q L (hardPrior q L hq hL) σ h
        (fun v => if testPrice q L (stateOf q L h) i ≤ v i then 1 else 0) = rho q L) ∧
    (∀ (i : Fin (bidderCount q L)) (j : Fin (L + 1)), stateOf q L h i = some j →
      condExpect q L (hardPrior q L hq hL) σ h (fun v => v i) ≤ y q L j.val / (1 - a q)) := by sorry

end TightClock
