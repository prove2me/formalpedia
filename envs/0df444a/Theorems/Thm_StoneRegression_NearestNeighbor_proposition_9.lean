-- Prove2me | Theorems.Thm_StoneRegression_NearestNeighbor_proposition_9
-- name    : StoneRegression.NearestNeighbor.proposition_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:38.732974+00:00
-- url     : https://prove2.me/theorems/5bfe2824-d12b-4d4c-8fb5-d351e1f2bf1a
-- title:
--   Proposition 9, p. 611 — as α ↓ 0, the ⌊αn⌋ nearest neighbors of X lie within any fixed distance δ
-- statement:
--   Let $\{s_n\}$ be a regular sequence of scales for the i.i.d. sequence $X, X_1, X_2, \dots$ in $\mathbb R^d$, with metrics $\rho_n$, and let $I_{n,t}(X)$ be the set of indices $i$ such that fewer than $\lfloor t\rfloor$ of $X_1,\dots,X_n$ are strictly $\rho_n$-closer to $X$ than $X_i$. Then for every $\delta > 0$,
--   $$\lim_{\alpha \downarrow 0}\ \limsup_{n\to\infty}\ P\Big(\max_{i \in I_{n,\alpha n}(X)} \|X_i - X\| > \delta\Big) = 0 .$$
--
--   In words: when only a vanishing fraction $\alpha$ of the sample counts as nearest neighbors, those neighbors are close to $X$ in the Euclidean norm, with probability close to one, for any distribution of $X$. This gives condition (3) for nearest neighbor weights whose coefficients have vanishing tails.
--
--   **Formalization Note** The paper's distance is called $a$; it is renamed $\delta$ here because $a$ is the constant of regularity. The maximum over an empty index set is read as "no index", so the event is "some $i \in I_{n,\alpha n}(X)$ has $\|X_i - X\| > \delta$". The $\limsup$ and the limit are taken in $[0,\infty]$, and $\alpha \downarrow 0$ is the limit from the right at $0$.
-- source:
--   Stone (1977), Ann. Statist. 5, Proposition 9, p. 611; proof pp. 611–612

import Mathlib
import Definitions.Def_StoneRegression_Criterion_Setting
import Definitions.Def_StoneRegression_NearestNeighbor_Weights

namespace StoneRegression.NearestNeighbor

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

theorem proposition_9 {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (s : ScaleSeq d) (a b : ℝ) (hs : IsRegular μ s a b) :
    ∀ δ : ℝ, 0 < δ →
      Tendsto (fun α : ℝ => limsup (fun n : ℕ => StoneRegression.Criterion.xLaw μ {ω | ∃ i ∈ nearIdx (s n (ω 0) (StoneRegression.Criterion.sample ω n)) (ω 0)
          (StoneRegression.Criterion.sample ω n) (α * n), δ < ‖ω (i.val + 1) - ω 0‖}) atTop) (𝓝[>] 0) (𝓝 0) := by sorry

end StoneRegression.NearestNeighbor
