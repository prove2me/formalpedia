-- Prove2me | Theorems.Thm_StochLinOpt_LowerBound_expectedRegret_ge_sqrt
-- name    : StochLinOpt.LowerBound.expectedRegret_ge_sqrt
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:36:45.610187+00:00
-- url     : https://prove2.me/theorems/684132e2-92c1-4e7d-98b8-92117461eb43
-- title:
--   Theorem 3 ($n=2$) — every algorithm has expected regret $\ge c\sqrt T$ on the circle
-- statement:
--   Consider stochastic linear optimization on the unit circle $D_2=S^1\subset\mathbb R^2$. The unknown mean $\mu$ is drawn uniformly from the circle $D_2/2$ of radius $1/2$, and when an algorithm plays $x_t\in D_2$ it observes a cost $\ell_t\in\{-1,+1\}$ with mean $\mu\cdot x_t$. The regret over $T$ rounds is $R=\sum_{t=1}^T(\mu\cdot x_t-\mu\cdot x^*)$ with $\mu\cdot x^*=\min_{x\in D_2}\mu\cdot x$.
--
--   There is a universal constant $c>0$ such that for every (possibly randomised) algorithm and every horizon $T\ge1$,
--   $$\mathbb E R=\mathbb E_\mu\,\mathbb E(R\mid\mu)\ \ge\ c\sqrt T,$$
--   where the inner expectation is over the observed costs (and the algorithm's internal randomness).
--
--   This is the lower half of the paper's characterisation of the minimax rate for stochastic linear bandits with decision sets of zero gap: no algorithm achieves a polylogarithmic regret on the circle, so the $O^*(\sqrt T)$ rate of ConfidenceBall₂ is tight in $T$.
--
--   **Formalization Note** The paper's Theorem 3 is stated for every even $n$ with $\mathbb E R\ge\frac1{10}n\sqrt T$. Only the case $n=2$ is proved (Section 6.1); the general case rests on Lemma 16, which is stated without proof, and as printed it is false for $n>10$, since on $D_n$ with $\mu\in D_n/n$ every round has regret at most $1$, so $\mathbb E R\le T<\frac1{10}n\sqrt T$ at $T=1$. This statement is the $n=2$ case with the constant left existential ($c$ is chosen before the algorithm and before $T$). The paper prints $\frac1{10}n\sqrt T=\frac15\sqrt T$ for $n=2$; its proof gives $c=\frac1{16}\min(\frac12-\frac1e,\frac1{64})=\frac1{1024}$ for $T$ large enough that $\varepsilon=T^{-1/4}\le3/16$ (the Freedman step needs $1/16$ in place of the printed $1/8$), and small $T$ is covered by the first round's expected regret $1/2$. The algorithm is a seeded policy (see the definition file); the expectation is exact over the $2^T$ cost strings.
-- source:
--   Dani, Hayes, Kakade, Stochastic Linear Optimization under Bandit Feedback, COLT 2008, PDF p. 6, Theorem 3 (Lower Bound), case n = 2; proof PDF pp. 11–12, Section 6.1

import Mathlib
import Definitions.Def_StochLinOpt_LowerBound_circleBandit

open MeasureTheory

namespace StochLinOpt.LowerBound

theorem expectedRegret_ge_sqrt :
    ∃ c : ℝ, 0 < c ∧
      ∀ (S : Type) [MeasurableSpace S] (ρ : Measure S) [IsProbabilityMeasure ρ]
        (π : RandomizedPolicy S) (T : ℕ), 1 ≤ T →
        c * Real.sqrt T ≤ expectedRegret ρ π T := by sorry

end StochLinOpt.LowerBound
