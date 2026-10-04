-- Prove2me | Theorems.Thm_StochApproxDyn_WeakAPT_conditional_drift_eq51
-- name    : StochApproxDyn.WeakAPT.conditional_drift_eq51
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T07:23:28.349823+00:00
-- url     : https://prove2.me/theorems/04a03a64-c8e5-4fd8-a4a9-f2e716a79adf
-- title:
--   Eq. (51): $E(U_{i+1}(f,T)-U_i(f\circ\Phi_T,T)\mid\mathcal F_{(i-1)T})\to0$ a.s. for a weak asymptotic pseudotrajectory
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a filtration $\{\mathcal F_t\}_{t\ge0}$, let $(M,d)$ be a separable metric space with its Borel $\sigma$-algebra, let $\Phi$ be a semiflow on $M$, and let $X$ be a weak asymptotic pseudotrajectory of $\Phi$. Let $f:M\to[0,1]$ be uniformly continuous, let $T>0$, and let $U_n(g,T)=\int_{(n-1)T}^{nT}g(X(s))\,ds$ for $n\ge1$ and $g=f$ or $g=f\circ\Phi_T$. Then, almost surely,
--   $$\lim_{i\to\infty}E\Big(U_{i+1}(f,T)-U_i(f\circ\Phi_T,T)\ \Big|\ \mathcal F_{(i-1)T}\Big)=0. \tag{51}$$
--
--   Since $U_{i+1}(f,T)-U_i(f\circ\Phi_T,T)=\int_{(i-1)T}^{iT}\big[f(X(s+T))-f(\Phi_T(X(s)))\big]\,ds$, this says that, conditionally on the past, the process over the next window is on average indistinguishable from the image under $\Phi_T$ of the process over the current window. This is the step of the proof of Theorem 10.1 where the weak asymptotic pseudotrajectory property enters.
--
--   **Formalization Note** Conditional expectations are Mathlib's `condExp`. The value at $i=0$ is irrelevant for the limit.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), DOI 10.1007/BFb0096509, Section 10, proof of Theorem 10.1, p. 62 (PDF p. 63), Eq. (51)

import Mathlib
import Definitions.Def_StochApproxDyn_WeakAPT_WeakAsymptoticPseudotrajectory
import Definitions.Def_StochApproxDyn_WeakAPT_BlockIntegral

namespace StochApproxDyn.WeakAPT

open MeasureTheory Filter Topology
open scoped NNReal

/-- Benaïm (1999), §10, proof of Theorem 10.1, Eq. (51), p. 62: if `X` is a weak asymptotic
pseudotrajectory of `Φ`, `f : M → [0, 1]` is uniformly continuous and `T > 0`, then almost surely
`E(U_{i+1}(f,T) - U_i(f ∘ Φ_T, T) | 𝓕_{(i-1)T}) → 0` as `i → ∞`. -/
theorem conditional_drift_eq51
    {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M] [TopologicalSpace.SeparableSpace M]
    [MeasurableSpace M] [BorelSpace M]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (Φ : Flow ℝ≥0 M) (X : ℝ≥0 → Ω → M)
    (hX : IsWeakAsymptoticPseudotrajectory P ℱ Φ X)
    (f : M → ℝ) (hf : UniformContinuous f) (hf01 : ∀ y, f y ∈ Set.Icc (0 : ℝ) 1)
    (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ ω ∂P, Tendsto
      (fun i : ℕ => (P[blockIntegral X f T (i + 1) - blockIntegral X (f ∘ Φ T) T i |
        ℱ (((i - 1 : ℕ) : ℝ≥0) * T)]) ω)
      atTop (𝓝 0) := by sorry

end StochApproxDyn.WeakAPT
