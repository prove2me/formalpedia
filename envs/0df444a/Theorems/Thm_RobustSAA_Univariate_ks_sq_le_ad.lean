-- Prove2me | Theorems.Thm_RobustSAA_Univariate_ks_sq_le_ad
-- name    : RobustSAA.Univariate.ks_sq_le_ad
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:17.265639+00:00
-- url     : https://prove2.me/theorems/e2354b85-dd12-4f5b-a364-5baa73b0f6c8
-- title:
--   §10.7, p. 39 — D_N²(F₀) ≤ max{1/√N + 3/(2N), √N A_N²(F₀) + 2/√N}
-- statement:
--   Let $N\ge1$, let $\xi^1,\dots,\xi^N\in\mathbb R$ have order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$, and let $F_0$ be a probability distribution on $\mathbb R$ with $0<F_0(\xi^{(i)})<1$ for every $i$. With $D_N$ the Kolmogorov–Smirnov statistic and
--
--   $$A_N^2(F_0)=-1-\sum_{i=1}^N\frac{2i-1}{N^2}\Big(\log F_0(\xi^{(i)})+\log\big(1-F_0(\xi^{(N+1-i)})\big)\Big)$$
--
--   the square of the Anderson–Darling statistic (8),
--
--   $$D_N^2(F_0)\le\max\Big\{\frac1{\sqrt N}+\frac3{2N},\ \sqrt N\,A_N^2(F_0)+\frac2{\sqrt N}\Big\}.$$
--
--   This is the bound for the CvM statistic with $W_N^2$ replaced by $A_N^2$; it reduces the AD test to the KS case.
--
--   **Formalization Note** Lean indices are 0-based and $\xi^{(N+1-i)}$ is `Fin.rev i`. The hypothesis $0<F_0(\xi^{(i)})<1$ is exactly the case in which $A_N$ is finite; otherwise $A_N=+\infty$ and $F_0$ lies in no AD region. The statement assumes $N\ge1$.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 39, sentence after the D_N² display

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 39: the bound of `ks_sq_le_cvm` with `W_N²` replaced by `A_N²`, whenever every
`F₀(ξ^(i))` lies in `(0, 1)` (the case in which `A_N` is finite). -/
theorem ks_sq_le_ad {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ)
    (hu : ∀ i, 0 < u F₀ s i ∧ u F₀ s i < 1) :
    ksStat F₀ s ^ 2 ≤
      max (1 / Real.sqrt N + 3 / (2 * N))
        (Real.sqrt N * adSq F₀ s + 2 / Real.sqrt N) := by sorry

end RobustSAA.Univariate
