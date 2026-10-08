-- Prove2me | Theorems.Thm_RadGauss_Kernel_lemma_22
-- name    : RadGauss.Kernel.lemma_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:28:36.145106+00:00
-- url     : https://prove2.me/theorems/5a9f56ba-d620-489a-80b8-37b0e85fd91c
-- title:
--   Lemma 22 — Ĝ_n(F) ≤ (2B/n)√(Σ k(X_i, X_i)) and R̂_n(F) ≤ (2B/n)√(Σ k(X_i, X_i)) for the kernel class
-- statement:
--   Let $k$ be a kernel on a compact space $\mathcal X$, let $B \ge 0$, and let $F$ be the class of kernel expansions $x \mapsto \sum_{i=1}^m \alpha_i k(x, x_i)$ with $\sum_{i,j}\alpha_i\alpha_j k(x_i, x_j) \le B^2$. Then for every $n$ and every sample $X_1, \dots, X_n \in \mathcal X$, the empirical Gaussian and Rademacher complexities of $F$ satisfy
--
--   $$\hat G_n(F) \le \frac{2B}{n}\sqrt{\sum_{i=1}^n k(X_i, X_i)}, \qquad \hat R_n(F) \le \frac{2B}{n}\sqrt{\sum_{i=1}^n k(X_i, X_i)}.$$
--
--   The bound depends on the sample only through the trace of its Gram matrix, so it holds for every realization of random elements $X_1, \dots, X_n$ and requires no bound on the kernel beyond its values at the sample points.
--
--   **Formalization Note** The statement is sample-wise: it holds for every $x : \mathrm{Fin}\,n \to \mathcal X$. Complexities are those of Definition 2 with values in $[0,\infty]$, the right-hand side is embedded by `ENNReal.ofReal`. The paper takes $B > 0$; here $B \ge 0$. At $n = 0$ both sides are $0$ ($2/0 = 0$ in Lean), so no $n \ge 1$ hypothesis is needed.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 477 (PDF p. 15), Lemma 22

import Mathlib
import Definitions.Def_RadGauss_Kernel_Complexity
import Definitions.Def_RadGauss_Kernel_KernelClass

namespace RadGauss.Kernel

/-- Lemma 22 (Bartlett–Mendelson 2002, p. 477). Let `k` be a kernel on `𝒳`, `B ≥ 0`, and let
`F = kernelClass k B`. For every sample `x_1, …, x_n ∈ 𝒳`,
`Ĝ_n(F) ≤ (2B/n) √(Σ_i k(x_i, x_i))` and `R̂_n(F) ≤ (2B/n) √(Σ_i k(x_i, x_i))`.
The paper takes `B > 0`; `0 ≤ B` is assumed here. At `n = 0` both sides are `0`. -/
theorem lemma_22 {X : Type*} [TopologicalSpace X] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) (x : Fin n → X) :
    empiricalGaussian (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) ∧
      RadGauss.Classification.empiricalRademacher (kernelClass k B) n x
        ≤ ENNReal.ofReal (2 * B / n * Real.sqrt (∑ i, k (x i) (x i))) := by sorry

end RadGauss.Kernel
