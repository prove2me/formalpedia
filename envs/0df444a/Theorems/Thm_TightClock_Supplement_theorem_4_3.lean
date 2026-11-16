-- Prove2me | Theorems.Thm_TightClock_Supplement_theorem_4_3
-- name    : TightClock.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:24:05.526423+00:00
-- url     : https://prove2.me/theorems/c958cfa3-782f-49a4-9395-e01e6aa54cea
-- title:
--   Theorem 4.3 — Auction 4 (Disjoint) is a prior-free 32-approximation
-- statement:
--   Let the bidders $[n]$ be partitioned into publicly known, pairwise disjoint groups $G_1,\dots,G_k$, where a set of bidders is feasible if and only if it is contained in one group, so the first-best welfare is $f(v)=\max_j v(G_j)$. Fix a public grid step $\delta>0$. Then Auction 4 (Disjoint), which runs MaxSample or LearnedPricesAuction with probability $1/2$ each, is a prior-free $32$-approximation in the public-grid model:
--
--   1. for every outcome of its randomness it is a clock auction for this family (it terminates with a feasible set of active bidders, all of whom are served);
--   2. for every value profile $v\in(\delta\mathbb Z_{\ge0})^n$,
--
--   $$\mathbb E[\mathrm{SW}]\ \ge\ \frac{1}{32}\,f(v),$$
--
--   the expectation being over the auction's internal randomness only.
--
--   Together with Theorem 5.1 this is the upper-bound side of the paper: a constant factor is achievable when the maximal feasible sets are disjoint, and Auction 4 is the black box used by Auction 9.
--
--   Differences from the source:
--   - generalization: ties broken "in a fixed order" (Auction 1, line 8) and "according to fixed public rules" (p.14); "Select arbitrary" maximizers (Auctions 6, 7) → the conclusion holds for every measurable selection rule `Selector n`, used for every arg max, arg min and fixed group; reason: every fixed tie-breaking order is such a rule, so the statement specializes to the page's; measurability is what makes the welfare a random variable with an expectation
--   - encoding: independent samples with probability $3/8$ and $1/4$, a fair coin, levels $r$ with probability $p_{j,r}$ → the seed space `DisjointSeed n` of independent uniforms on $[0,1]$ (product law); a coin of bias $p$ is $u<p$, the level is drawn by the inverse distribution function; reason: the same joint law of all draws
--   - encoding: $\mathbb E[\mathrm{SW}]$ over the auction's internal randomness → a Bochner integral over the seed, with integrability as a conjunct; `clockWelfare` is $0$ on a non-terminating run; no payments; reason: p.14 evaluates clocks only through welfare and gives non-terminating runs no service; integrability makes the integral meaningful
--   - reading: the auction is a (randomized) clock auction under the §3 rules → the conjunct `IsStrictClock` for every seed: the published validity rules, every active bidder served at the stop, and termination on every nonnegative profile; reason: §3 (p.13): "The auction terminates with a feasible set of active bidders, all of whom are served"; the published `IsValidClock` is the relaxed §6.1 class, so the strict rule is stated explicitly
--   - encoding: simultaneous offers within one step, reveals of the sampled bidders, raises inside RetainOnly → made one at a time in the order of the bidder indices; reason: the outcome does not depend on the order
--   - encoding: bidders partitioned into groups $G_1,\dots,G_k$; feasible iff inside one group → `Gs : Finset (Finset (Fin n))`, pairwise disjoint, nonempty, covering `Fin n`; family `groupFamily Gs` (with $\emptyset$); reason: a partition of $[n]$ indexed by its blocks; $f(v)=\max_j v(G_j)$ is `firstBest` of this family on nonnegative profiles
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Theorem 4.3, §4.3, p.19 (PDF p.22)

import Mathlib
import Definitions.Def_TightClock_Supplement_disjointProg
import Definitions.Def_TightClock_Supplement_ClockProg_toStrategy
import Definitions.Def_TightClock_Supplement_IsStrictClock
import Definitions.Def_TightClock_Supplement_IsGridProfile
import Definitions.Def_TightClock_Supplement_groupFamily
import Definitions.Def_TightClock_firstBest
import Definitions.Def_TightClock_clockWelfare

set_option autoImplicit false

open MeasureTheory

namespace TightClock.Supplement

/-- Theorem 4.3: Auction 4 (`Disjoint`) is a prior-free 32-approximation. For pairwise disjoint,
nonempty groups covering the bidders, a grid step `δ > 0` and every measurable `arg max` selection rule (ties), every
seed gives a clock auction for the group family under the strict rules of §3, and for every value
profile on the grid `δℤ≥0` the expected welfare over the seed is at least `f(v)/32`, where
`f(v) = max_j v(G_j)`. Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*,
manuscript (STOC 2027 submission), Theorem 4.3, §4.3, p.19 (PDF 22): "Auction 4 is a prior-free
32-approximation: for every value profile, E[SW] ≥ 1/32 f(v)."

**Formalization Note** The seed space is `DisjointSeed n` with the product of uniform laws
(`volume`); the expectation is a Bochner integral and its integrability is part of the conclusion.
A run that never stops has welfare `0` (`clockWelfare`). -/
theorem theorem_4_3 {n : ℕ} (Gs : Finset (Finset (Fin n)))
    (hdisj : (Gs : Set (Finset (Fin n))).PairwiseDisjoint id)
    (hne : ∀ G ∈ Gs, G.Nonempty) (hcover : ∀ i : Fin n, ∃ G ∈ Gs, i ∈ G)
    (δ : ℝ) (hδ : 0 < δ) (sel : Selector n) :
    (∀ ω : DisjointSeed n, IsStrictClock (groupFamily Gs) (disjointProg δ Gs sel ω).toStrategy) ∧
    ∀ v : Fin n → ℝ, IsGridProfile δ v →
      Integrable (fun ω : DisjointSeed n => clockWelfare (disjointProg δ Gs sel ω).toStrategy v) ∧
      firstBest (groupFamily Gs) v / 32 ≤
        ∫ ω : DisjointSeed n, clockWelfare (disjointProg δ Gs sel ω).toStrategy v := by sorry

end TightClock.Supplement
