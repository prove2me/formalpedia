-- Prove2me | Theorems.Thm_TightClock_Supplement_theorem_5_1
-- name    : TightClock.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:25:26.059393+00:00
-- url     : https://prove2.me/theorems/74281a7b-1cec-4c75-8ef0-cfa0f4fa9938
-- title:
--   Theorem 5.1 — FourBranch achieves $f(v)/(40960\beta_m)$, an $O(\log\log k/\log\log\log k)$-approximation
-- statement:
--   Let $\mathcal F\subseteq 2^{[n]}$ be a nonempty downward-closed family with every singleton feasible, with maximal sets $G_1,\dots,G_k$ and maximum overlap $d$. Let $m=\lceil\log(8d)\rceil$ and let $\beta_m>1$ solve $\beta_m\log\beta_m-\beta_m+1=\log(4m)$ (5.1). Fix a public grid step $\delta>0$. Auction 10 (FourBranch) satisfies:
--
--   1. for every outcome of its randomness it is a clock auction for $\mathcal F$, and for every value profile $v\in(\delta\mathbb Z_{\ge0})^n$,
--
--   $$\mathbb E[\mathrm{SW}]\ \ge\ \frac{f(v)}{40960\,\beta_m};$$
--
--   2. its approximation factor is $O(\log\log d/\log\log\log d)$: there are constants $C>0$ and $d_0$ such that every such instance with $d\ge d_0$ has $\mathbb E[\mathrm{SW}]\ge f(v)\log\log\log d/(C\log\log d)$;
--   3. since $d\le k$, its approximation factor is $O(\log\log k/\log\log\log k)$: there are $C'>0$ and $k_0$ such that every such instance with $k\ge k_0$ has $\mathbb E[\mathrm{SW}]\ge f(v)\log\log\log k/(C'\log\log k)$.
--
--   Logarithms are natural. With Theorem 6.1, the mission goal, this shows that $\Theta(\log\log k/\log\log\log k)$ is the optimal approximation factor of clock auctions for downward-closed feasibility.
--
--   Differences from the source:
--   - generalization: ties broken "in a fixed order" (Auction 1, line 8) and "according to fixed public rules" (p.14); "Select arbitrary" maximizers (Auctions 6, 7) → the conclusion holds for every measurable selection rule `Selector n`, used for every arg max, arg min and fixed group; reason: every fixed tie-breaking order is such a rule, so the statement specializes to the page's; measurability is what makes the welfare a random variable with an expectation
--   - encoding: independent samples with probability $1/2$, the screening coin $\lambda_1/\lambda$, draws from $H_1$ and $H_2(x)$, a uniformly random ordering of $G_1,\dots,G_k$, a uniform $\kappa\in\{1,2,3,4\}$, fresh randomness for Auction 4 → the seed space `FourBranchSeed n` of independent uniforms on $[0,1]$ (product law); $H_1$, $H_2(x)$ by their quantile functions; the ordering by i.i.d. uniform keys; $\kappa$ from one uniform; reason: the same joint law of all draws (ties of keys have probability $0$)
--   - encoding: $\mathbb E[\mathrm{SW}]$ over the auction's internal randomness → a Bochner integral over the seed, with integrability as a conjunct; `clockWelfare` is $0$ on a non-terminating run; no payments; reason: p.14 evaluates clocks only through welfare and gives non-terminating runs no service; integrability makes the integral meaningful
--   - reading: the auction is a (randomized) clock auction under the §3 rules → the conjunct `IsStrictClock` for every seed: the published validity rules, every active bidder served at the stop, and termination on every nonnegative profile; reason: §3 (p.13): "The auction terminates with a feasible set of active bidders, all of whom are served"; the published `IsValidClock` is the relaxed §6.1 class, so the strict rule is stated explicitly
--   - encoding: simultaneous offers within one step, reveals of the sampled bidders, raises inside RetainOnly → made one at a time in the order of the bidder indices; reason: the outcome does not depend on the order
--   - encoding: Singleton sweeps the bidders "in a fixed order" → the order of the bidder indices; reason: any fixed order becomes this one after relabeling the bidders, and the statement quantifies over all families and profiles
--   - encoding: approximation factor $O(\log\log d/\log\log\log d)$, and $O(\log\log k/\log\log\log k)$ → some $C>0$ and threshold $d_0$ (resp. $k_0$), chosen before the instance, with $\mathbb E[\mathrm{SW}]\ge f(v)\log\log\log d/(C\log\log d)$ for every instance with $d\ge d_0$ (resp. with $k$ in place of $d$); reason: the meaning of a worst-case approximation factor $O(\cdot)$; natural logarithms (the base only changes $C$)
--   - encoding: $\beta_m$ the unique solution of (5.1), with $m=\lceil\log(8d)\rceil$ → `betaM F` = `betaRoot (log (4 * headSize F))`, which is $1$ when no root exists; reason: a root exists and is unique whenever $d\ge1$ (proved in the verification file); $d=0$ only without bidders, where $f(v)=0$
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Theorem 5.1, §5, p.22 (PDF p.25); restated and proved pp.32–33 (PDF pp.35–36)

import Mathlib
import Definitions.Def_TightClock_Supplement_fourBranch
import Definitions.Def_TightClock_Supplement_ClockProg_toStrategy
import Definitions.Def_TightClock_Supplement_IsStrictClock
import Definitions.Def_TightClock_Supplement_IsGridProfile
import Definitions.Def_TightClock_Supplement_betaM
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_TightClock_overlap
import Definitions.Def_TightClock_firstBest
import Definitions.Def_TightClock_clockWelfare

set_option autoImplicit false

open MeasureTheory

namespace TightClock.Supplement

/-- Theorem 5.1: `FourBranch` (Auction 10). For every nonempty downward-closed `F` with every
singleton feasible, every grid step `δ > 0` and every measurable `arg max` selection rule `sel` (ties):

1. every seed gives a clock auction for `F` under the strict rules of §3, and for every value profile
   on the grid `δℤ≥0`, `E[SW] ≥ f(v)/(40960 β_m)`, with `m = ⌈log(8d)⌉` and `β_m` from (5.1);
2. its approximation factor is `O(log log d / log log log d)`: some `C > 0` and `d₀` give
   `E[SW] ≥ f(v) log log log d / (C log log d)` on every instance with overlap `d ≥ d₀`;
3. likewise `O(log log k / log log log k)` in the number `k` of maximal feasible sets.

Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC 2027
submission), Theorem 5.1, §5, p.22 (PDF 25), restated and proved p.32–33 (PDF 35–36).

**Formalization Note** Natural logarithms throughout. The seed space is `FourBranchSeed n` with the
product of uniform laws (`volume`); the expectation is a Bochner integral, integrable by clause 1.
A run that never stops has welfare `0`. In clauses 2 and 3 the constants are chosen before the
instance (uniform worst-case bounds). -/
theorem theorem_5_1 :
    (∀ {n : ℕ} (F : Finset (Finset (Fin n))), BayesClock.IsDownwardClosed F →
      (∀ i : Fin n, {i} ∈ F) → ∀ δ : ℝ, 0 < δ → ∀ sel : Selector n,
        (∀ ω : FourBranchSeed n, IsStrictClock F (fourBranch δ F sel ω).toStrategy) ∧
        ∀ v : Fin n → ℝ, IsGridProfile δ v →
          Integrable (fun ω : FourBranchSeed n => clockWelfare (fourBranch δ F sel ω).toStrategy v) ∧
          firstBest F v / (40960 * betaM F) ≤
            ∫ ω : FourBranchSeed n, clockWelfare (fourBranch δ F sel ω).toStrategy v) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ d₀ : ℕ, ∀ {n : ℕ} (F : Finset (Finset (Fin n))),
      BayesClock.IsDownwardClosed F → (∀ i : Fin n, {i} ∈ F) → d₀ ≤ overlap F →
      ∀ δ : ℝ, 0 < δ → ∀ (sel : Selector n) (v : Fin n → ℝ), IsGridProfile δ v →
        firstBest F v * Real.log (Real.log (Real.log (overlap F : ℝ))) /
            (C * Real.log (Real.log (overlap F : ℝ))) ≤
          ∫ ω : FourBranchSeed n, clockWelfare (fourBranch δ F sel ω).toStrategy v) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ {n : ℕ} (F : Finset (Finset (Fin n))),
      BayesClock.IsDownwardClosed F → (∀ i : Fin n, {i} ∈ F) →
      k₀ ≤ (BayesClock.maximalSets F).card →
      ∀ δ : ℝ, 0 < δ → ∀ (sel : Selector n) (v : Fin n → ℝ), IsGridProfile δ v →
        firstBest F v * Real.log (Real.log (Real.log ((BayesClock.maximalSets F).card : ℝ))) /
            (C * Real.log (Real.log ((BayesClock.maximalSets F).card : ℝ))) ≤
          ∫ ω : FourBranchSeed n, clockWelfare (fourBranch δ F sel ω).toStrategy v) := by sorry

end TightClock.Supplement
