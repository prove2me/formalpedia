-- Prove2me | Theorems.Thm_TalagrandThinning_theorem_1_2
-- name    : TalagrandThinning.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:43:29.796577+00:00
-- url     : https://prove2.me/theorems/c6f5397a-c503-40a9-af2c-d960f490936e
-- title:
--   Theorem 1.2 — domination after thinning
-- statement:
--   Let $0<t,q<1$ and let $\nu$ be a $q$-spread probability law on $\{0,1\}^N$, for any $N$. Then:
--
--   1. for every $p\in(0,1)$ with
--   $$\eta:=\frac{tq(1-p)}{p(1-t)}\le1,\qquad(1.3)$$
--   the retention law is dominated: $T_t\nu\le_d\mu_p$;
--   2. in particular
--   $$T_t\nu\le_d\mu_{p_*},\qquad p_*:=\frac{tq}{1-t+tq}.\qquad(1.4)$$
--
--   The assertion is uniform in the dimension $N$: no constant depends on $N$.
--
--   This is the main theorem of the note; Talagrand's thinning conjecture (Corollary 1.3) is the case $t=\alpha$, $q=\alpha p$.
--
--   **Formalization Note** $\le_d$ is the coupling definition (`StochDomSubset`). $N$ is arbitrary, including $N=0$. That $p_*\in(0,1)$ follows from $0<t,q<1$ and is not assumed.
--
--   Differences from the source:
--   - encoding: subsets $A\subseteq[N]=\{1,\dots,N\}$, $\cap$, $\subseteq$ → indicator vectors $x:\mathrm{Fin}\,N\to\mathrm{Bool}$ on $\{0,\dots,N-1\}$, $\sqcap$, $\le$; reason: the paper identifies a set with its indicator vector (p.2); relabelling the ground set changes no instance
--   - encoding: $\rho\le_d\sigma$: a coupling $(A,B)$ with $A\subseteq B$ a.s. → `StochDomSubset`: a probability measure on pairs with marginals $\rho,\sigma$ giving mass $0$ to $\{A\not\subseteq B\}$; reason: the paper's coupling definition (p.2) written as a measure on pairs
--   - encoding: a random set $J\sim\nu$, an independent mask $X_t\sim\mu_t$ and $T_t\nu=\mathcal L(J\cap X_t)$ → a probability measure `ν` on the cube, `prodLaw N t` (the weighted sum of point masses $\sum_x\mu_t(\{x\})\delta_x$) and `retention t ν`, the push-forward of the product measure `ν.prod (prodLaw N t)` under $(J,x)\mapsto J\sqcap x$; reason: laws of random sets on a finite cube, independence as the product measure; same instances
-- source:
--   Fang & Wang, A Note on a Result of Chen Li: the Thinning Problem via the Kernel Method, arXiv:2609.18458 (held version dated Sep 12, 2026, sha256 68a0f38d…), Theorem 1.2, eqs. (1.3)–(1.4), p.2

import Mathlib
import Definitions.Def_TalagrandThinning_IsSpread
import Definitions.Def_TalagrandThinning_retention
import Definitions.Def_TalagrandThinning_StochDomSubset

set_option autoImplicit false

open MeasureTheory

namespace TalagrandThinning

/-- Theorem 1.2 (Domination after thinning)
(arXiv:2609.18458, held version dated Sep 12, 2026, sha256 68a0f38d…, Theorem 1.2, eqs. (1.3)–(1.4), p.2).

Let `0 < t, q < 1` and let `ν` be a `q`-spread probability law on `{0,1}^N` (any `N`). Then
(1) for every `p ∈ (0,1)` with `η := tq(1 − p)/(p(1 − t)) ≤ 1` (1.3), `T_t ν ≤_d µ_p`;
(2) `T_t ν ≤_d µ_{p*}` with `p* := tq/(1 − t + tq)` (1.4).

**Formalization Note** `≤_d` is `StochDomSubset`, the coupling definition of p.2. `N : ℕ` is
arbitrary (including `N = 0`): "the assertion is uniform in the dimension `N`". `p* ∈ (0,1)` is a
consequence of `0 < t, q < 1`, not a hypothesis. -/
theorem theorem_1_2 {N : ℕ} (t q : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (hq0 : 0 < q) (hq1 : q < 1)
    (ν : Measure (Cube N)) [IsProbabilityMeasure ν] (hν : IsSpread q ν) :
    (∀ p : ℝ, 0 < p → p < 1 → t * q * (1 - p) / (p * (1 - t)) ≤ 1 →
      StochDomSubset (retention t ν) (prodLaw N p)) ∧
    StochDomSubset (retention t ν) (prodLaw N (t * q / (1 - t + t * q))) := by sorry

end TalagrandThinning
