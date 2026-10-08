-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_theorem_2
-- name    : StoneRegression.NearestNeighbor.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:12.827814+00:00
-- url     : https://prove2.me/theorems/289cb6b6-b138-4e78-8de0-d07c64f04576
-- title:
--   Theorem 2, p. 600 — nearest neighbor weights with vanishing tails and c_{n1} → 0 are consistent
-- statement:
--   Let $X, X_1, X_2, \dots$ be i.i.d. $\mathbb R^d$-valued with an **arbitrary** law $\mu$, and let $\{s_n\}$ be a regular sequence of scales with metrics $\rho_n$. For $n \ge 1$ let $c_{n1} \ge \dots \ge c_{nn} \ge 0$ with $\sum_i c_{ni} = 1$ ($c_{ni} = 0$ for $i > n$), and let $W_n$ be the corresponding nearest neighbor probability weight function (8). If
--   $$\lim_{n\to\infty} \sum_{i > \alpha n} c_{ni} = 0 \quad \text{for all } \alpha > 0 \qquad\text{and}\qquad \lim_{n\to\infty} c_{n1} = 0,$$
--   then $\{W_n\}$ is consistent: whenever $(X,Y), (X_1,Y_1), \dots$ are i.i.d., $Y$ is real, $r \ge 1$ and $E|Y|^r < \infty$,
--   $$\lim_{n\to\infty} E\Big|\sum_{i=1}^n W_{ni}(X) Y_i - E(Y\mid X)\Big|^r = 0 .$$
--
--   This is Stone's universal consistency theorem for nearest neighbor regression: the uniform, triangular and quadratic $k_n$-nearest neighbor estimates with $k_n \to \infty$ and $k_n/n \to 0$ are consistent in $L^r$ for every distribution of $(X,Y)$ with $E|Y|^r < \infty$, with no density, continuity or support assumption.
--
--   **Formalization Note** "Whenever the pairs are i.i.d." is encoded by quantifying over every Markov kernel giving the conditional law of $Y$ given $X$ (see the setting file). Regularity of the scales is the standing assumption of §3 (p. 599) and is a hypothesis; it includes measurability of the scales (added) and condition (7) read for all points. The tail sum $\sum_{i>\alpha n} c_{ni}$ is finite because $c_{ni} = 0$ for $i > n$; it is written as a sum over $\alpha n < i \le n$.
-- source:
--   Stone (1977), Ann. Statist. 5, Theorem 2, p. 600; standing assumption p. 599; proof §11, pp. 611–615

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem theorem_2 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b)
    (c : ℕ → ℕ → ℝ) (hc : ∀ n, 1 ≤ n → IsCoeffRow c n)
    (htail : ∀ α : ℝ, 0 < α →
      Tendsto (fun n : ℕ => ∑ i ∈ (Finset.Icc 1 n).filter (fun i : ℕ => α * n < (i : ℝ)), c n i) atTop (𝓝 0))
    (hfirst : Tendsto (fun n => c n 1) atTop (𝓝 0)) :
    StoneRegression.Criterion.IsConsistent μ (nnWeights c s) := by sorry

end StoneRegression.NearestNeighbor
