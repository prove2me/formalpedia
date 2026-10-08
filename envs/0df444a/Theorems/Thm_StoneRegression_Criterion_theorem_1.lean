-- Prove2me | Theorems.Thm_StoneRegression_Criterion_theorem_1
-- name    : StoneRegression.Criterion.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:44:04.969692+00:00
-- url     : https://prove2.me/theorems/2a244eee-ae9b-4469-8dc6-8d7d11f75c1a
-- title:
--   Theorem 1, p. 598 — (1)–(5) imply consistency; consistency implies (4), (5), and (3), (1) for nonnegative weights
-- statement:
--   Let $X, X_1, X_2,\dots$ be i.i.d. $\mathbb R^d$-valued random variables with law $\mu$, and let $\{W_n\}$ be a sequence of Borel weights $W_{ni}(X) = W_{ni}(X, X_1,\dots,X_n)$, $1\le i\le n$. Consider the conditions
--
--   1. there is a $C\ge1$ such that for every nonnegative Borel function $f$ on $\mathbb R^d$, $\ E\sum_i|W_{ni}(X)|f(X_i)\le C\,Ef(X)\ $ for all $n\ge1$;
--   2. there is a $D\ge1$ such that $\ P\big(\sum_i|W_{ni}(X)|\le D\big) = 1\ $ for all $n\ge1$;
--   3. $\sum_i|W_{ni}(X)|\,I_{\{\|X_i - X\|>a\}}\to0$ in probability for all $a>0$;
--   4. $\sum_i W_{ni}(X)\to1$ in probability;
--   5. $\max_i|W_{ni}(X)|\to0$ in probability.
--
--   Recall that $\{W_n\}$ is **consistent** if, whenever $(X,Y),(X_1,Y_1),(X_2,Y_2),\dots$ are i.i.d. with $Y$ real valued, $r\ge1$ and $E|Y|^r<\infty$, the estimator $\hat E_n(Y\mid X) = \sum_i W_{ni}(X)Y_i$ satisfies
--   $$\lim_{n\to\infty} E\,\big|\hat E_n(Y\mid X) - E(Y\mid X)\big|^r = 0 .$$
--
--   **Theorem 1.** The following hold.
--
--   1. If (1)–(5) are satisfied, then $\{W_n\}$ is consistent.
--   2. If $\{W_n\}$ is consistent, then (4) and (5) hold.
--   3. If $\{W_n\}$ is consistent and $W_n\ge0$ for all $n\ge1$, then (3) holds.
--   4. If $\{W_n\}$ is consistent, $W_n\ge0$ for all $n\ge1$, and (2) holds, then (1) holds.
--
--   The theorem characterizes, in terms of the distribution of $X$ alone, which local-averaging rules estimate every regression function consistently in every $L^r$; for probability weights (2) and (4) are automatic and (1), (3), (5) become necessary and sufficient (Corollary 1). It is the foundation for the universal consistency of nearest-neighbor weights (Theorem 2) and for the conditional-quantile and Bayes-rule results of the paper.
--
--   **Formalization Note.** Consistency quantifies over every Markov kernel $\kappa$ (the conditional law of $Y$ given $X$), every real $r\ge1$ and every $\kappa$ with $E|Y|^r<\infty$; this covers every i.i.d. sequence of pairs with $X$-marginal $\mu$. The p. 596 assumption that standard normal variables independent of the $X$'s are available, which the paper says is needed for the necessity of (5), is supplied by the kernel $\kappa\equiv N(0,1)$. The weights are assumed jointly Borel in $(x, x_1, \dots, x_n)$, which the paper leaves implicit. Expectations of nonnegative quantities are lower Lebesgue integrals in $[0,\infty]$, and the constant $C$ is a nonnegative real. Sample indices are $0$-based. "$W_n\ge0$" is pointwise nonnegativity of every weight. The definition of consistency on p. 597 prints "$r>1$"; the proof of Theorem 1 (p. 611, (13)) establishes the conclusion for every $r\ge1$, which is the reading used here.
-- source:
--   Stone (1977), Ann. Statist. 5, Theorem 1, p. 598; proof §10, pp. 607–611

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace StoneRegression.Criterion

/-- Theorem 1 (Stone 1977, p. 598). (i) Conditions (1)–(5) imply consistency. (ii) Consistency implies
(4) and (5). (iii) Consistent nonnegative weights satisfy (3). (iv) Consistent nonnegative weights
satisfying (2) satisfy (1). -/
theorem theorem_1 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (W : WeightSeq d) (hW : MeasurableWeights W) :
    ((∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) → (∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) →
        Cond3 μ W → Cond4 μ W → Cond5 μ W → IsConsistent μ W) ∧
    (IsConsistent μ W → Cond4 μ W ∧ Cond5 μ W) ∧
    (IsConsistent μ W → Nonneg W → Cond3 μ W) ∧
    (IsConsistent μ W → Nonneg W → (∃ D : ℝ, 1 ≤ D ∧ Cond2 μ W D) →
        ∃ C : ℝ≥0, 1 ≤ C ∧ Cond1 μ W C) := by sorry

end StoneRegression.Criterion
