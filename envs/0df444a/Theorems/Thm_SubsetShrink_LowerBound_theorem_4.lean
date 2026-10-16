-- Prove2me | Theorems.Thm_SubsetShrink_LowerBound_theorem_4
-- name    : SubsetShrink.LowerBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T21:26:48.750616+00:00
-- url     : https://prove2.me/theorems/79b25c90-544b-4c9c-b2b3-56f9ca93c6bf
-- title:
--   Theorem 4, p. 18 — at low SNR, every best-subsets solution has ‖Xβ̂ − Xβ*‖² ≳ σ²γ_k²k log(ep/k) w.h.p. (pinned 2 ≤ k, β* ∈ B0(k))
-- statement:
--   Consider the linear model $y=X\beta^*+\epsilon$, where $X$ is a deterministic real $n\times p$ matrix whose columns have unit Euclidean norm, $\beta^*\in\mathbb R^p$, and $\epsilon$ has independent $N(0,\sigma^2)$ entries with $\sigma>0$. Let $\gamma_k$ be the minimal $k$-sparse eigenvalue of $X$, and let $\hat\beta_{\ell_0}$ denote any solution of the best-subsets problem
--   $$
--   \hat\beta_{\ell_0}\in\arg\min\ \|y-X\beta\|^2\quad\text{s.t.}\quad\|\beta\|_0\le k .
--   $$
--   There are universal constants $c_0,c,C>0$ such that the following holds. Suppose that $2\le k\le p$, that $\|\beta^*\|_0\le k$, and that
--   $$
--   \|\beta^*\|\le c_0\,\sigma\,\gamma_k\sqrt{k\log(ep/k)} .
--   $$
--   Then, with probability at least
--   $$
--   1-2\Big(\frac{ep}{k}\Big)^{-c\gamma_k^2k}-\Big(\frac{ep}{k}\Big)^{-k},
--   $$
--   every best-subsets solution $\hat\beta_{\ell_0}$ satisfies
--   $$
--   \|X\hat\beta_{\ell_0}-X\beta^*\|^2\ \ge\ C\,\sigma^2\gamma_k^2\,k\log(ep/k) .
--   $$
--
--   In the low signal-to-noise regime the best-subsets prediction error is therefore of order at least $\sigma^2\gamma_k^2k\log(ep/k)$; combined with the paper's upper bounds this shows that its fast-rate bound is tight there, while the shrinkage estimators enjoy slow rates that are smaller in that regime.
--
--   **Formalization Note** "$\|\beta^*\|/\sigma\lesssim\gamma_k\sqrt{k\log(ep/k)}$ with a sufficiently small universal constant" is the hypothesis with an existentially quantified $c_0$; $c_0$, the exponent constant $c$ and the factor $C$ hidden in $\gtrsim$ are all quantified before $n,p,X,\sigma,k,\beta^*$. Two hypotheses are added to the printed statement. (i) $k\ge2$ instead of $k\in[p]$: for $k=1$ the statement is false (all columns equal to $e_1$ and $\beta^*=0$ give an error $\epsilon_1^2$, of order $\sigma^2$, while the bound demands order $\sigma^2\log(ep)$ with probability tending to one as $p\to\infty$). (ii) $\|\beta^*\|_0\le k$: the proof uses a bound on $\|\beta^*\|_1$, which the printed bound on $\|\beta^*\|$ implies only for sparse $\beta^*$, and §3.4 sets the theorem in Corollary 1's setting $f^*=X\beta^*$ with $\beta^*\in B_0(k)$. "With probability at least $1-\eta$" is the existence of a measurable set $A$ of noise vectors with $\mathbb P(A)\ge1-\eta$ on which *every* minimizer obeys the bound; no minimizer is chosen and existence is not assumed. Powers with real exponents have the positive base $ep/k\ge e$; logarithms are natural and $e=\exp(1)$.
-- source:
--   Mazumder, Radchenko & Dedieu, Subset Selection with Shrinkage, arXiv:1708.03288v4, p. 18, §3.4, Theorem 4; proof B.9, pp. 44–46

import Mathlib
import Definitions.Def_SubsetShrink_LowerBound_Model

namespace SubsetShrink.LowerBound

/-- Theorem 4, p. 18 (pinned `2 ≤ k ≤ p` and `β* ∈ B0(k)`): if `‖β*‖ ≤ c₀ σ γ_k √(k log(ep/k))` with a
sufficiently small universal `c₀`, then with probability at least
`1 − 2(ep/k)^{−c γ_k² k} − (ep/k)^{−k}` every best-subsets solution `β̂` of (1) for `y = Xβ* + ε`
satisfies `‖Xβ̂ − Xβ*‖² ≥ C σ² γ_k² k log(ep/k)`; `c₀`, `c`, `C` are universal. -/
theorem theorem_4 :
    ∃ c0 c C : ℝ, 0 < c0 ∧ 0 < c ∧ 0 < C ∧
      ∀ {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (σ : ℝ) (k : ℕ) (βstar : Fin p → ℝ),
        SubsetShrink.Events.UnitCols X → 0 < σ → 2 ≤ k → k ≤ p → l0 βstar ≤ k →
        SubsetShrink.Events.l2 βstar ≤ c0 * σ * SubsetShrink.L2.gam X k * Real.sqrt (k * Real.log (Real.exp 1 * p / k)) →
        ∃ A : Set (Fin n → ℝ), MeasurableSet A ∧
          (∀ ε ∈ A, ∀ βhat : Fin p → ℝ, IsBestSubset X (X.mulVec βstar + ε) k βhat →
            C * (σ ^ 2 * SubsetShrink.L2.gam X k ^ 2 * k * Real.log (Real.exp 1 * p / k)) ≤
              ∑ i, (X.mulVec βhat i - X.mulVec βstar i) ^ 2) ∧
          1 - 2 * (Real.exp 1 * p / k) ^ (-(c * SubsetShrink.L2.gam X k ^ 2 * k)) -
              (Real.exp 1 * p / k) ^ (-(k : ℝ)) ≤
            (SubsetShrink.Events.noiseLaw n σ A).toReal := by sorry

end SubsetShrink.LowerBound
