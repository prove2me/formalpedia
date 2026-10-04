-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_block_average_tendsto_eq53
-- name    : StochApproxDyn.WeakAPT.block_average_tendsto_eq53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:22:58.116979+00:00
-- url     : https://prove2.me/theorems/ab792d21-1c3a-43b4-be70-93a28a39d196
-- title:
--   Eq. (53): block averages converge along a weakly convergent subsequence of occupation measures
-- statement:
--   Let $(M,d)$ be a metric space with its Borel $\sigma$-algebra and let $x:\mathbb R_+\to M$ be a Borel measurable path, with occupation measures $\mu_t=\frac1t\int_0^t\delta_{x(s)}\,ds$ for $t>0$. Let $T>0$, let $t_j\to\infty$ be a sequence of times and $\mu\in\mathcal P(M)$, and suppose $\mu_{t_j}\to\mu$ weakly. Put $n_j=\lfloor t_j/T\rfloor$, the integer part of $t_j/T$. Then for every bounded continuous $f:M\to\mathbb R$
--   $$\lim_{j\to\infty}\frac1{n_jT}\sum_{i=0}^{n_j-1}\int_{iT}^{(i+1)T}f(x_s)\,ds=\int_M f(x)\,\mu(dx). \tag{53}$$
--
--   This is the deterministic link between the block integrals of the proof of Theorem 10.1 and the limit points of the occupation measures: averages of complete windows of length $T$ have the same limit as the occupation measures themselves.
--
--   **Formalization Note** The statement is for a single fixed path; in the proof of Theorem 10.1 it is applied to $x=X(\cdot,\omega)$ and a sequence $t_j$ along which $\mu_{t_j}(\omega)\to\mu$, whose existence for a limit point $\mu$ the paper takes from metrizability of $\mathcal P(M)$. Weak convergence is convergence in Mathlib's `ProbabilityMeasure M`. For the finitely many $j$ with $n_j=0$ the left side is $0$ (Lean's convention $1/0=0$); this does not affect the limit.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 63 (PDF p. 64), Eq. (53)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_OccupationMeasure

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (53), p. 63 (deterministic, one path): if the
occupation measures `μ_{t_j}` of a measurable path `x` converge weakly to `μ` along `t_j → ∞`, and
`n_j = ⌊t_j / T⌋`, then for every bounded continuous `f : M → ℝ`
`(1/(n_j T)) ∑_{i=0}^{n_j - 1} ∫_{iT}^{(i+1)T} f(x_s) ds → ∫_M f dμ`. -/
theorem block_average_tendsto_eq53
    {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (x : ℝ≥0 → M) (hx : Measurable x) (T : ℝ≥0) (hT : 0 < T)
    (t : ℕ → ℝ≥0) (ht : Tendsto t atTop atTop) (μ : ProbabilityMeasure M)
    (hμ : Tendsto (fun j => occupationMeasure x (t j)) atTop (𝓝 μ))
    (f : M → ℝ) (hf : Continuous f) (hfb : ∃ C : ℝ, ∀ y, |f y| ≤ C) :
    Tendsto
      (fun j : ℕ => (1 / ((⌊t j / T⌋₊ : ℝ) * T)) *
        ∑ i ∈ Finset.range ⌊t j / T⌋₊, ∫ s in (i : ℝ) * T..((i : ℝ) + 1) * T, f (x s.toNNReal))
      atTop (𝓝 (∫ y, f y ∂(μ : Measure M))) := by sorry

end StochApproxDyn.WeakAPT
