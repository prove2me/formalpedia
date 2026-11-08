-- Prove2me | Theorems.Thm_TightClock_theorem_6_12
-- name    : TightClock.theorem_6_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:23:36.426202+00:00
-- url     : https://prove2.me/theorems/0203f38b-8394-4638-94f8-38a92a5e23f0
-- title:
--   Theorem 6.12 — explicit lower bound
-- statement:
--   Fix an integer $q\ge8$. For all sufficiently large $L$, some realization $\mathcal F$ of Instance 11, with parameters as in (6.1), satisfies
--
--   $$\mathrm{FB}(\mathcal F,D)\ge\Big(1-\varepsilon_L-\frac{2}{n^2}\Big)LB\quad\text{and}\quad\mathrm{CB}(\mathcal F,D)\le\Big(R_q+\frac{3}{a(1-a)B}\Big)B.$$
--
--   Moreover,
--
--   $$\log n=L\log L+O(L),\qquad \log\log\bar K_L\le L\log L+O(L),$$
--
--   where the constants implicit in $O(\cdot)$ depend only on $q$. The same realization has at most $\bar K_L$ maximal feasible sets (p.36) and every singleton feasible.
--
--   The welfare ratio approaches $L/R_q$ while the instance size grows on the scale $L\log L$, which gives Theorem 6.1.
--
--   Differences from the source:
--   - encoding: the depth $L$ of the tree, with levels $r=1,\dots,L$ in Instance 11 → the hypothesis `1 ≤ L`; reason: at $L=0$ there are no bidders and $h=a^2B/L$ divides by zero; the page's construction has $L\ge1$
--   - reading: §3, p.13: "We assume without loss of generality that $\{i\}\in\mathcal F$ for every bidder $i$"; the proof of Theorem 6.1 does not check this for its family → `∀ i, {i} ∈ F` is part of the conclusion; reason: removing unservable bidders would lower $n$, so the stronger reading is kept: $\Pr[i\text{ in no leaf}]\le L(1-a)^{K_1}$ per bidder, a failure absorbed by the slack in Lemma 6.3's Markov step
--   - generalization: the clock of §3, which serves its whole active set when that set terminates the auction → the wider class of §6.1, in which offers may continue after feasibility and any feasible subset of the active set may be served; prices are arbitrary nonnegative reals and rounds are unbounded; reason: p.34 widens the class for this upper bound; a bound over the wider class implies it for the §3 clocks, which are members
--   - encoding: a clock has a measurable public seed, with payments → seed space in `Type`, welfare at each nonnegative profile measurable in the seed, no payments, and welfare $0$ on a non-terminating run; reason: p.14 evaluates clocks only through welfare and gives non-terminating runs no service; the measurability makes the expectation meaningful
--   - encoding: $\mathbb E_{X\sim D}$ over an i.i.d. prior $D$ on $[n]$ → `priorExpect` over one `FinitePrior`, with bidders `Fin n`; reason: the law is finite, so the expectation is a finite sum, and one marginal gives i.i.d. by construction
--   - encoding: $\log n=L\log L+O(L)$ and $\log\log\bar K_L\le L\log L+O(L)$ → $|\log n-L\log L|\le cL$ and $\log\log\bar K_L\le L\log L+cL$ for $L\ge L_0$, with $c$ chosen after $q$ and before $L$; reason: this is the meaning of the $O(\cdot)$ on the page, with constants depending only on $q$
--   - generalization: Theorem 6.12 does not restate the count of maximal sets → the conjunct `(maximalSets (familyOf T)).card ≤ K̄_L` for the chosen realization; reason: p.36 states it for every realization ("F has at most $\bar K_L$ maximal sets") and Theorem 6.1's proof uses it; dropping the conjunct gives the page's statement
-- source:
--   Afshinmehr, Ascher, Ashuri, Gkatzelis, Mahmoudkhan, Rubinstein, Schoepflin, Tight Approximation Bounds for Clock Auctions, manuscript (STOC 2027 submission; held artifact sha256 29bccd9c…b31b, preprint basis), Theorem 6.12, §6.7, p.48 (PDF p.51)

import Mathlib
import Definitions.Def_TightClock_FB
import Definitions.Def_TightClock_CB
import Definitions.Def_TightClock_familyOf
import Definitions.Def_TightClock_hardPrior
import Definitions.Def_TightClock_epsL
import Definitions.Def_TightClock_Rq
import Definitions.Def_TightClock_KBar
import Definitions.Def_BayesClock_maximalSets

set_option autoImplicit false

namespace TightClock

/-- Theorem 6.12 (Explicit lower bound), p.48 (PDF 51), of Afshinmehr et al., manuscript (STOC 2027 submission): fix an
integer `q ≥ 8`. For all sufficiently large `L`, some realization `F` of Instance 11 satisfies
`FB(F, D) ≥ (1 − ε_L − 2/n²) L B` and `CB(F, D) ≤ (R_q + 3/(a (1 − a) B)) B`. Moreover,
`log n = L log L + O(L)` and `log log K̄_L ≤ L log L + O(L)`, with constants depending only on `q`.

**Formalization Note** The count of maximal sets is stated on p.36 (PDF 39). The singleton clause is the reading of
§3, p.13 (PDF 16), recorded in the differences. The constant `c` is chosen after `q` and before `L`. -/
theorem theorem_6_12 (q : ℕ) (hq : 8 ≤ q) :
    ∃ (c : ℝ) (L₀ : ℕ), ∀ (L : ℕ) (hL : 1 ≤ L), L₀ ≤ L →
      (∃ T : Tree q L,
        (1 - epsL q L - 2 / ((bidderCount q L : ℝ) ^ 2)) * ((L : ℝ) * (B L : ℝ)) ≤
          FB (familyOf T) (hardPrior q L hq hL) ∧
        CB (familyOf T) (hardPrior q L hq hL) ≤
          (Rq q + 3 / (a q * (1 - a q) * (B L : ℝ))) * (B L : ℝ) ∧
        (BayesClock.maximalSets (familyOf T)).card ≤ KBar q L L ∧
        ∀ i : Fin (bidderCount q L), {i} ∈ familyOf T) ∧
      |Real.log (bidderCount q L : ℝ) - (L : ℝ) * Real.log (L : ℝ)| ≤ c * (L : ℝ) ∧
      Real.log (Real.log (KBar q L L : ℝ)) ≤ (L : ℝ) * Real.log (L : ℝ) + c * (L : ℝ) := by sorry

end TightClock
