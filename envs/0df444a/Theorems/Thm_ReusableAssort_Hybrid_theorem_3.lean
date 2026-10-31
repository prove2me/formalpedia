-- Prove2me | Theorems.Thm_ReusableAssort_Hybrid_theorem_3
-- name    : ReusableAssort.Hybrid.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:18.318571+00:00
-- url     : https://prove2.me/theorems/cc32d949-4852-45de-a5f9-6c845d889686
-- title:
--   Theorem 3, p. 20 — Sim+Hybrid(i) is (1 − min{1/2, ε*(c_min)})-competitive against Expected-LP
-- statement:
--   Consider Bayesian online assortment of reusable resources: $n \ge 1$ products with integer inventories $c_i \ge 1$, consumers arriving at times $1, \dots, T$ with independent types $z_t \sim F_t$, weakly substitutable choice models on a downward-closed family $\mathcal S$ of assortments, nonnegative fees and rental durations on $\{1, \dots, T\}$. Let $y^*$ be an optimal solution of the Bayesian expected LP Expected-LP$[\{F_t\}_{t=1}^T]$ with $\sum_{S \in \mathcal S} y^*_{S,t,z} = 1$ for all $t, z$, and let $\gamma^*(x)$ denote a minimizer of (1) for each $x$.
--
--   Sim+Hybrid(i) samples $\hat S \sim y^*_{\cdot,t,z_t}$, discards each product $i \in \hat S$ that has no unit on hand, otherwise discards it at random with probability $\gamma^*(c_i)$ if $\mathcal R_i + \varepsilon^*(c_i) < 1$ ("large inventory") and by the revenue thresholds of the optimistic DP if not ("small inventory"), and offers the output of sub-assortment sampling. Its expected revenue satisfies
--   $$\mathbb E[\mathrm{Rev}] \ \ge\ \Big(1 - \min\Big\{\tfrac12, \varepsilon^*(c_{\min})\Big\}\Big) \cdot \mathrm{LP}(y^*),$$
--   where $c_{\min} = \min_i c_i$ and $\varepsilon^*(x) = \min_{\gamma \in [0,1]} 1 - (1-\gamma)(1 - \exp(-\gamma^2 x/(2-\gamma)))$.
--
--   The ratio $1 - \min\{1/2, \varepsilon^*(c_{\min})\} = \max\{1/2, 1 - \varepsilon^*(c_{\min})\}$ is the better of the guarantees of Theorems 1 and 2, achieved by a single algorithm; it tends to $1$ as $c_{\min} \to \infty$ and never falls below $1/2$.
--
--   **Formalization Note** The competitive ratio of Definition 1 is written as $\alpha \cdot \mathrm{LP}(y^*) \le \mathbb E[\mathrm{Rev}]$ for every instance and every optimal normalized $y^*$. The discarding probability of a large-inventory product is not specified on the page; it is taken to be a minimizer $\gamma^*(c_i)$ of (1) at $x = c_i$ (the label compares $\mathcal R_i$ with $1 - \varepsilon^*(c_i)$; with $\gamma^*(c_{\min})$ the theorem would fail). Added hypotheses, all part of the model's reading: one finite type space for all times, durations in $\{1, \dots, T\}$ with $\bar G(k) = \Pr[d > k]$, $\phi^z(S, \cdot)$ a sub-probability supported on $S$, weak substitutability for $S \cup \{j\} \in \mathcal S$, $\mathcal S$ nonempty and downward closed, $r \ge 0$, $c_i \ge 1$, $n \ge 1$. Procedure 1 breaks ties among equal ratios by product index.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 20, Theorem 3

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_Algorithms

namespace ReusableAssort.Hybrid

theorem theorem_3 {n T : ℕ} [NeZero n] {Z : Type} [Fintype Z] [DecidableEq Z]
    (I : Instance n T Z) (hI : I.Assumptions)
    (y : ℕ → Z → Finset (Fin n) → ℝ) (hy : LPOptimal I y) (hN : Normalized I y)
    (gam : ℕ → ℝ) (hgam : ∀ x : ℕ, IsGammaStar (x : ℝ) (gam x)) :
    (1 - min (1 / 2) (epsStar (cmin I : ℝ))) * lpObj I y
      ≤ expRev I y (hybrid I y gam) 1 (fun _ _ => 0) := by sorry

end ReusableAssort.Hybrid
