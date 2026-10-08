-- Prove2me | Theorems.Thm_RadGauss_Kernel_complexity_bound
-- name    : RadGauss.Kernel.complexity_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T16:28:45.313211+00:00
-- url     : https://prove2.me/theorems/73898060-a8a4-480a-8119-b72649bd5ff2
-- title:
--   §4.3, p. 478 — R_n(F) ≤ 2B√(E k(X,X)/n) and G_n(F) ≤ 2B√(E k(X,X)/n) for kernel expansions with α′Kα ≤ B²
-- statement:
--   Let $\mathcal X$ be a compact space with its Borel $\sigma$-algebra, $\mu$ a probability measure on $\mathcal X$, $k$ a kernel on $\mathcal X$, $B \ge 0$, and $F$ the class of kernel expansions $x \mapsto \sum_{i=1}^m \alpha_i k(x, x_i)$ ($m \in \mathbb N$, $x_i \in \mathcal X$) with $\sum_{i,j}\alpha_i\alpha_j k(x_i, x_j) \le B^2$. Let $X \sim \mu$ and let $X_1, \dots, X_n$ be an i.i.d. sample from $\mu$. Then for every $n$
--
--   $$R_n(F) = \mathbb E\hat R_n(F) \le 2B\sqrt{\frac{\mathbb E\,k(X, X)}{n}}, \qquad G_n(F) = \mathbb E\hat G_n(F) \le 2B\sqrt{\frac{\mathbb E\,k(X, X)}{n}}.$$
--
--   The quantity $\mathbb E\,k(X,X)$ is the trace of the integral operator $T_k f = \int k(\cdot, y) f(y)\, d\mu(y)$ on $L_2(\mu)$, so the complexity of the kernel class decays like $n^{-1/2}$ with a constant governed by that trace; combined with the paper's risk bounds this gives margin bounds for kernel methods such as support vector machines.
--
--   **Formalization Note** $R_n$ and $G_n$ are the Definition 2 complexities with values in $[0,\infty]$ (lower Lebesgue integrals over $\mu^{\otimes n}$), so no integrability or measurability hypothesis on $\hat R_n(F)$ or $\hat G_n(F)$ is assumed or needed; the right-hand side is embedded by `ENNReal.ofReal`. $\mathbb E\,k(X,X) = \int k(x,x)\,d\mu(x)$ is a Bochner integral of a continuous function on a compact space, hence genuine. The paper takes $B > 0$; here $B \ge 0$. At $n = 0$ both sides are $0$, so no $n \ge 1$ hypothesis is needed.
-- source:
--   Bartlett, Mendelson, Rademacher and Gaussian Complexities: Risk Bounds and Structural Results, J. Mach. Learn. Res. 3 (2002), p. 478 (PDF p. 16), §4.3, display after the proof of Lemma 22

import Mathlib
import Definitions.Def_RadGauss_Kernel_Complexity
import Definitions.Def_RadGauss_Kernel_KernelClass

open MeasureTheory

namespace RadGauss.Kernel

/-- §4.3, p. 478 (Bartlett–Mendelson 2002), the display after the proof of Lemma 22. Let `k` be a
kernel on the compact space `𝒳` (with its Borel σ-algebra), `μ` a probability measure on `𝒳`,
`B ≥ 0`, and `F = kernelClass k B`. Then for every `n`,
`R_n(F) = E R̂_n(F) ≤ 2B √(E k(X, X) / n)` and `G_n(F) = E Ĝ_n(F) ≤ 2B √(E k(X, X) / n)`,
where `X ∼ μ`. The paper takes `B > 0`; `0 ≤ B` is assumed here. At `n = 0` both sides are `0`. -/
theorem complexity_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (k : X → X → ℝ) (hk : IsKernel k)
    (B : ℝ) (hB : 0 ≤ B) (n : ℕ) :
    RadGauss.Classification.rademacherComplexity μ n (kernelClass k B)
        ≤ ENNReal.ofReal (2 * B * Real.sqrt ((∫ x, k x x ∂μ) / n)) ∧
      RadGauss.LipschitzGaussian.gaussianComplexity μ n (kernelClass k B)
        ≤ ENNReal.ofReal (2 * B * Real.sqrt ((∫ x, k x x ∂μ) / n)) := by sorry

end RadGauss.Kernel
