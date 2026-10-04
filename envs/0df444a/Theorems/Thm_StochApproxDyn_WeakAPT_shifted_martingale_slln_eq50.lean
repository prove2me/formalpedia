-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_shifted_martingale_slln_eq50
-- name    : StochApproxDyn.WeakAPT.shifted_martingale_slln_eq50
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:23:29.808037+00:00
-- url     : https://prove2.me/theorems/9ebd0730-bd0f-4d1c-a931-3ee9ca71bf34
-- title:
--   Eq. (50): $\frac1n\sum_{i=1}^n[U_{i+1}(f,T)-E(U_{i+1}(f,T)\mid\mathcal F_{(i-1)T})]\to0$ a.s.
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\{\mathcal F_t\}_{t\ge0}$, let $(M,d)$ be a separable metric space with its Borel $\sigma$-algebra, and let $X:\mathbb R_+\times\Omega\to M$ be progressively measurable. Let $f:M\to[0,1]$ be uniformly continuous, let $T>0$, and let $U_n(f,T)=\int_{(n-1)T}^{nT}f(X(s))\,ds$ for $n\ge1$. Then, almost surely,
--   $$\lim_{n\to\infty}\frac1n\sum_{i=1}^n\Big[U_{i+1}(f,T)-E\big(U_{i+1}(f,T)\mid\mathcal F_{(i-1)T}\big)\Big]=0. \tag{50}$$
--
--   This is the analogue of (47) with conditioning two windows back instead of one; together with (51) it lets one compare the block integrals of $f$ in window $i+1$ with those of $f\circ\Phi_T$ in window $i$.
--
--   **Formalization Note** Only progressive measurability of $X$ is assumed; condition (ii) of a weak asymptotic pseudotrajectory is not needed. Conditional expectations are Mathlib's `condExp`; the index $i$ runs over $1,\dots,n$ and $\mathcal F_{(i-1)T}$ is evaluated at $i\ge1$ only.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 62 (PDF p. 63), Eq. (50)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (50), p. 62: for a progressively measurable
process `X`, a uniformly continuous `f : M → [0, 1]` and `T > 0`, almost surely
`(1/n) ∑_{i=1}^n [U_{i+1}(f,T) - E(U_{i+1}(f,T) | 𝓕_{(i-1)T})] → 0`. -/
theorem shifted_martingale_slln_eq50
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T (i + 1) ω -
          (P[blockIntegral X f T (i + 1) | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT
