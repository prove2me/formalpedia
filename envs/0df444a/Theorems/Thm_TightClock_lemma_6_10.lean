-- Prove2me | Theorems.Thm_TightClock_lemma_6_10
-- name    : TightClock.lemma_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:38:24.207799+00:00
-- url     : https://prove2.me/theorems/28894968-8ca7-4da8-a4c8-021b78a8ba70
-- title:
--   Lemma 6.10 — the potential does not grow
-- statement:
--   On a good tree, every step of every single-step clock satisfies
--
--   $$\mathbb E[\Phi(J^{t+1})\mid H^t]\le\Phi(J^t).$$
--
--   Moreover,
--
--   $$\Phi(J^0)=\log A_{\mathrm{root}}(J^0)+3.$$
--
--   So each test pays for its own adaptation: the increase in the logarithmic tracked mass is covered by the reserve lost when the tested bidder declines.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - encoding: a clock auction after the §6.2 reduction, with tree and seed part of $H^t$ → a valid deterministic `SingleStepStrategy`, with tree and seed fixed parameters; reason: the seed and the tree are fixed before the conditioning, as in the proof of Proposition 6.11; the prior is independent of both
--   - encoding: $\mathbb E[\cdot\mid H^t]$ → `condExpect`, the ratio of two finite sums, at a history $h$ of positive probability; reason: the law is finite, and a history of probability zero is not conditioned on
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Lemma 6.10, §6.6, p.45 (PDF p.48)

import Mathlib
import Definitions.Def_TightClock_potential
import Definitions.Def_TightClock_IsGoodTree
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_IsValidSingleStep
import Definitions.Def_TightClock_condExpect
import Definitions.Def_TightClock_account

set_option autoImplicit false

namespace TightClock

/-- Lemma 6.10 (The potential does not grow), p.45 (PDF 48), of Afshinmehr et al., manuscript (STOC 2027 submission): on a
good tree, every step of every single-step clock satisfies `E[Φ(Jᵗ⁺¹) | Hᵗ] ≤ Φ(Jᵗ)`, and
`Φ(J⁰) = log A_root(J⁰) + 3`. -/
theorem lemma_6_10 (q L : ℕ) (hq : 8 ≤ q) (hL : 1 ≤ L) (T : Tree q L) (hT : IsGoodTree T) :
    (∀ σ : SingleStepStrategy (bidderCount q L), IsValidSingleStep q L (familyOf T) σ →
      ∀ h : SingleStepHistory (bidderCount q L), 0 < histProb q L (hardPrior q L hq hL) σ h →
        condExpect q L (hardPrior q L hq hL) σ h
            (fun v => potential T (stateOf q L (ssHist q L σ v (h.length + 1)))) ≤
          potential T (stateOf q L h)) ∧
    potential T (initialState q L) =
      Real.log (account T (rootNode q L) (initialState q L)) + 3 := by sorry

end TightClock
