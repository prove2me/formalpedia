-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_block_average_difference_eq52
-- name    : StochApproxDyn.WeakAPT.block_average_difference_eq52
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:23:51.933604+00:00
-- url     : https://prove2.me/theorems/5c4bf169-793a-4cdc-9005-0e0163a8f6a2
-- title:
--   Eq. (52): $\frac1n\sum_{i=1}^n U_{i+1}(f,T)-\frac1n\sum_{i=1}^n U_i(f\circ\Phi_T,T)\to0$ a.s.
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\{\mathcal F_t\}_{t\ge0}$, let $(M,d)$ be a separable metric space with its Borel $\sigma$-algebra, let $\Phi$ be a semiflow on $M$, and let $X$ be a weak asymptotic pseudotrajectory of $\Phi$. Let $f:M\to[0,1]$ be uniformly continuous, let $T>0$, and let $U_n(g,T)=\int_{(n-1)T}^{nT}g(X(s))\,ds$ for $n\ge1$. Then there is a set $\Omega(f,T)\subset\Omega$ of full measure such that for all $\omega\in\Omega(f,T)$
--   $$\lim_{n\to\infty}\ \frac1n\sum_{i=1}^n U_{i+1}(f,T)-\frac1n\sum_{i=1}^n U_i(f\circ\Phi_T,T)=0. \tag{52}$$
--
--   In words: along almost every path, the time average of $f$ and the time average of $f\circ\Phi_T$ over the first $nT$ units of time differ by $o(n)$ after normalisation by $n$. Combined with weak convergence of occupation measures (Eq. (53)), this yields $\int f\circ\Phi_T\,d\mu=\int f\,d\mu$ for every limit point $\mu$.
--
--   **Formalization Note** "There is a set of full measure on which ..." is stated as "for $P$-almost every $\omega$ ...".
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 63 (PDF p. 64), Eq. (52)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (52), p. 63: if `X` is a weak asymptotic
pseudotrajectory of `Φ`, `f : M → [0, 1]` is uniformly continuous and `T > 0`, then almost surely
`(1/n) ∑_{i=1}^n U_{i+1}(f,T) - (1/n) ∑_{i=1}^n U_i(f ∘ Φ_T, T) → 0`. -/
theorem block_average_difference_eq52
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X f T (i + 1) ω -
        (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n, blockIntegral X (f ∘ Φ T) T i ω)
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT
