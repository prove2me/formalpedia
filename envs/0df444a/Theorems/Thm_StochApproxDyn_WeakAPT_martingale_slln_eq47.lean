-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_martingale_slln_eq47
-- name    : StochApproxDyn.WeakAPT.martingale_slln_eq47
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:23:05.234279+00:00
-- url     : https://prove2.me/theorems/24625982-308f-4b8f-8586-1933286abd3a
-- title:
--   Eq. (47): $\frac1n\sum_{i=1}^n[U_i(f,T)-E(U_i(f,T)\mid\mathcal F_{(i-1)T})]\to0$ a.s.
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\{\mathcal F_t\}_{t\ge0}$, let $(M,d)$ be a separable metric space with its Borel $\sigma$-algebra, and let $X:\mathbb R_+\times\Omega\to M$ be progressively measurable. Let $f:M\to[0,1]$ be continuous, let $T>0$, and let
--   $$U_n(f,T)=\int_{(n-1)T}^{nT}f(X(s))\,ds\qquad(n\ge1).$$
--   Then, almost surely,
--   $$\lim_{n\to\infty}\frac1n\sum_{i=1}^n\Big[U_i(f,T)-E\big(U_i(f,T)\mid\mathcal F_{(i-1)T}\big)\Big]=0. \tag{47}$$
--
--   This is a strong law of large numbers for the bounded martingale differences $U_i-E(U_i\mid\mathcal F_{(i-1)T})$; it lets the block averages of $f$ along the path be replaced by averages of their one-step conditional expectations.
--
--   **Formalization Note** The paper states (47) for the uniformly continuous $f$ fixed in the proof, and then applies it "with $f\circ\Phi_T$ in lieu of $f$" (p. 63), which is continuous but in general not uniformly continuous; the statement is therefore given for every continuous $f$ with values in $[0,1]$, which covers both uses. Only progressive measurability of $X$ is assumed; condition (ii) of a weak asymptotic pseudotrajectory is not needed. Conditional expectations are Mathlib's `condExp`.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 62 (PDF p. 63), Eq. (47)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (47), p. 62: for a progressively measurable
process `X`, a continuous `f : M → [0, 1]` and `T > 0`, almost surely
`(1/n) ∑_{i=1}^n [U_i(f,T) - E(U_i(f,T) | 𝓕_{(i-1)T})] → 0`. -/
theorem martingale_slln_eq47
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (hX : IsProgressivelyMeasurable ℱ X)
    (f : M → ℝ) (hf : Continuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => (1 / (n : ℝ)) * ∑ i ∈ Finset.Icc 1 n,
        (blockIntegral X f T i ω - (P[blockIntegral X f T i | ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω))
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT
