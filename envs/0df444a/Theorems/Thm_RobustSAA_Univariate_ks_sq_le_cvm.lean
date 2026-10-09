-- Prove2me | Theorems.Thm_RobustSAA_Univariate_ks_sq_le_cvm
-- name    : RobustSAA.Univariate.ks_sq_le_cvm
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:15.969181+00:00
-- url     : https://prove2.me/theorems/cbc70904-5cf5-4048-8264-3b2a7ce31ee1
-- title:
--   §10.7, p. 39 — D_N²(F₀) ≤ max{1/√N + 3/(2N), √N W_N²(F₀) + 2/√N}
-- statement:
--   Let $N\ge1$, let $\xi^1,\dots,\xi^N\in\mathbb R$ have order statistics $\xi^{(1)}\le\dots\le\xi^{(N)}$, and let $F_0$ be a probability distribution on $\mathbb R$. With $D_N$ the Kolmogorov–Smirnov and $W_N$ the Cramér–von Mises statistic (8),
--
--   $$D_N^2(F_0)\le\max\Big\{\frac1{\sqrt N}+\frac3{2N},\ \sqrt N\,W_N^2(F_0)+\frac2{\sqrt N}\Big\}.$$
--
--   Hence a CvM threshold of order $N^{-1/2}$ forces $D_N\to0$ uniformly over the CvM region, reducing the CvM test to the KS case.
--
--   **Formalization Note** Lean indices are 0-based (Lean's `i` is the paper's $i+1$), and the order statistics are the sorted sample `s ∘ Tuple.sort s`. The statement assumes $N\ge1$, which the paper's statistics presuppose.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, §10.7, proof of Theorem 5, p. 39, display after "Therefore,"

import Mathlib
import Definitions.Def_RobustSAA_Univariate_Setting

namespace RobustSAA.Univariate

open Filter MeasureTheory

/-- §10.7, p. 39: `D_N²(F₀) ≤ max{1/√N + 3/(2N), √N W_N²(F₀) + 2/√N}`. -/
theorem ks_sq_le_cvm {N : ℕ} (hN : 0 < N) (F₀ : ProbabilityMeasure ℝ) (s : Fin N → ℝ) :
    ksStat F₀ s ^ 2 ≤
      max (1 / Real.sqrt N + 3 / (2 * N))
        (Real.sqrt N * cvmStat F₀ s ^ 2 + 2 / Real.sqrt N) := by sorry

end RobustSAA.Univariate
