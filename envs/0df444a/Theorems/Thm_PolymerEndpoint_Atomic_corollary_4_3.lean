-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_corollary_4_3
-- name    : PolymerEndpoint.Atomic.corollary_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:36:52.236847+00:00
-- url     : https://prove2.me/theorems/f5425931-5351-4022-815d-951966854de8
-- title:
--   Corollary 4.3 — empirical endpoint laws approach the fixed points of 𝒯
-- statement:
--   Throughout, $d\geq1$; the disorder law $\mathfrak L$ is a non-degenerate probability measure on $\mathbb R$ with $\lambda(\alpha)=\log\mathbb E e^{\alpha X}<\infty$ for all $\alpha\in[-2\beta,2\beta]$ (the paper's (1.1)). Let $\beta>0$, let $(X_u)$ be an i.i.d. environment with law $\mathfrak L$, let $f_i$ be the endpoint probability mass function of the length-$i$ polymer, viewed as an element of the space $\mathcal S$ of partitioned subprobability measures, and let
--
--   $$
--   \mu_n=\frac1n\sum_{i=0}^{n-1}\delta_{f_i}
--   $$
--
--   be the empirical measure (4.1). Let $\mathcal K=\{\nu\in\mathcal P(\mathcal S):\mathcal T\nu=\nu\}$ be the set of fixed points of the update map (4.5), and $\mathcal W(\mu,\mathcal K)=\inf_{\nu\in\mathcal K}\mathcal W(\mu,\nu)$ the Wasserstein distance to it. Then
--
--   $$
--   \mathcal W(\mu_n,\mathcal K)\longrightarrow0\qquad\text{almost surely as }n\to\infty.
--   $$
--
--   This is the first step from the polymer to the abstract fixed-point equation: every limit point of the empirical endpoint laws is invariant under $\mathcal T$.
--
--   **Formalization Note** The distance to a set is an infimum in $[0,\infty]$, so the empty set would give $+\infty$, not $0$. The standing range is $\beta>0$ (§1.1).
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 32, Corollary 4.3 (with (4.1), p. 30 and (4.5), p. 32)

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter Finset
open scoped BigOperators ENNReal Topology

namespace PolymerEndpoint.Atomic

theorem corollary_4_3 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    ∀ᵐ a ∂P, Tendsto
      (fun n : ℕ => Wdist (empirical X β n a) (K (d := d) 𝔏 β))
      atTop (𝓝 0) := by sorry

end PolymerEndpoint.Atomic
