-- Prove2me | Theorems.Thm_TightClock_theorem_6_1
-- name    : TightClock.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:21:54.624968+00:00
-- url     : https://prove2.me/theorems/8ed9268c-5184-4845-ba66-418f714d196a
-- title:
--   Theorem 6.1 — no clock auction beats $\gamma\log\log k/\log\log\log k$ or $\gamma\log n/\log\log n$
-- statement:
--   For every $\gamma<1$ and every sufficiently large integer $k$, there exists a downward-closed family $\mathcal F$ with at most $k$ maximal feasible sets (so every bidder belongs to at most $k$ of them) and an i.i.d. prior $D$ supported on finitely many points of a public grid, such that
--
--   $$\mathrm{FB}(\mathcal F,D)>\gamma\,\frac{\log\log k}{\log\log\log k}\,\mathrm{CB}(\mathcal F,D).$$
--
--   Moreover, for every $\gamma<1$ there are such instances with $n$ bidders for arbitrarily large $n$ and
--
--   $$\mathrm{FB}(\mathcal F,D)>\gamma\,\frac{\log n}{\log\log n}\,\mathrm{CB}(\mathcal F,D).$$
--
--   Here $\mathrm{FB}$ is the expected first-best welfare, and $\mathrm{CB}$ is the supremum of the expected welfare over all adaptive randomized clock auctions, which know $\mathcal F$ and $D$. So clock auctions cannot reach a constant approximation of the first best, even with randomization and a known i.i.d. prior, and the ratio matches the upper bound of the paper's FourBranch auction up to a constant factor.
--
--   **Formalization Note** Logarithms are natural, and "sufficiently large" and "arbitrarily large" are written with explicit thresholds $k_0$ and $N_0$, which also exclude the junk values of `Real.log` at small arguments.
--
--   Differences from the source:
--   - reading: §3, p.13: "We assume without loss of generality that $\{i\}\in\mathcal F$ for every bidder $i$"; the proof of Theorem 6.1 does not check this for its family → `∀ i, {i} ∈ F` is part of the conclusion; reason: removing unservable bidders would lower $n$, so the stronger reading is kept: $\Pr[i\text{ in no leaf}]\le L(1-a)^{K_1}$ per bidder, a failure absorbed by the slack in Lemma 6.3's Markov step
--   - generalization: the clock of §3, which serves its whole active set when that set terminates the auction → the wider class of §6.1, in which offers may continue after feasibility and any feasible subset of the active set may be served; prices are arbitrary nonnegative reals and rounds are unbounded; reason: p.34 widens the class for this upper bound; a bound over the wider class implies it for the §3 clocks, which are members
--   - encoding: a clock has a measurable public seed, with payments → seed space in `Type`, welfare at each nonnegative profile measurable in the seed, no payments, and welfare $0$ on a non-terminating run; reason: p.14 evaluates clocks only through welfare and gives non-terminating runs no service; the measurability makes the expectation meaningful
--   - encoding: $\mathbb E_{X\sim D}$ over an i.i.d. prior $D$ on $[n]$ → `priorExpect` over one `FinitePrior`, with bidders `Fin n`; reason: the law is finite, so the expectation is a finite sum, and one marginal gives i.i.d. by construction
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Theorem 6.1, §6.1, p.34 (PDF p.37)

import Mathlib
import Definitions.Def_BayesClock_IsDownwardClosed
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_TightClock_overlap
import Definitions.Def_TightClock_IsOnGrid
import Definitions.Def_TightClock_FB
import Definitions.Def_TightClock_CB

set_option autoImplicit false

namespace TightClock

/-- Theorem 6.1, p.34 (PDF 37), of Afshinmehr et al., *Tight Approximation Bounds for Clock Auctions*, manuscript (STOC
2027 submission): for every `γ < 1` and every sufficiently large integer `k`, there exists a downward-closed family `F`
with at most `k` maximal feasible sets (so every bidder belongs to at most `k` of them) and an i.i.d. prior `D` supported
on finitely many points of a public grid, such that `FB(F, D) > γ (log log k / log log log k) CB(F, D)`. Moreover, for
every `γ < 1` there are such instances with `n` bidders for arbitrarily large `n` and
`FB(F, D) > γ (log n / log log n) CB(F, D)`.

**Formalization Note** Logarithms are natural, as the proof requires. `CB` is the supremum over all adaptive randomized
clocks, with real prices and unbounded rounds. The thresholds `k₀` and `N₀` exclude the junk values of `Real.log` at
small arguments. -/
theorem theorem_6_1 (γ : ℝ) (hγ : γ < 1) :
    (∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ (n : ℕ) (F : Finset (Finset (Fin n))) (D : FinitePrior),
        BayesClock.IsDownwardClosed F ∧ (∀ i : Fin n, {i} ∈ F) ∧
        (BayesClock.maximalSets F).card ≤ k ∧ overlap F ≤ k ∧ IsOnGrid D ∧
        γ * (Real.log (Real.log (k : ℝ)) / Real.log (Real.log (Real.log (k : ℝ)))) * CB F D < FB F D) ∧
    (∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      ∃ (F : Finset (Finset (Fin n))) (D : FinitePrior),
        BayesClock.IsDownwardClosed F ∧ (∀ i : Fin n, {i} ∈ F) ∧ IsOnGrid D ∧
        γ * (Real.log (n : ℝ) / Real.log (Real.log (n : ℝ))) * CB F D < FB F D) := by sorry

end TightClock
