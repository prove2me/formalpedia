-- Prove2me | Theorems.Thm_PolymerEndpoint_Atomic_theorem_4_9
-- name    : PolymerEndpoint.Atomic.theorem_4_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T03:40:49.61301+00:00
-- url     : https://prove2.me/theorems/dcf76c1f-6859-41fc-840d-0f5ace7f11de
-- title:
--   Theorem 4.9 — empirical laws approach minimizing fixed points
-- statement:
--   Let $\mu_n$ be the empirical law of the first $n$ polymer endpoint distributions and $\mathcal M$ the invariant laws minimizing the energy functional. Under the standing model and moment assumptions,
--   $$
--   \mathcal W(\mu_n,\mathcal M)\longrightarrow0\qquad\text{almost surely}.
--   $$
--
--   This identifies the possible long-run empirical states with the minimizing fixed-point set.
--
--   **Formalization Note** The standing range is $\beta>0$ (§1.1). The disorder law is non-degenerate and satisfies (1.1) on $[-2\beta,2\beta]$; $d\geq1$.
-- source:
--   Bates and Chatterjee, The endpoint distribution of directed polymers, arXiv:1612.03443v5, p. 37, Theorem 4.9

import Definitions.Def_PolymerEndpoint_Atomic_Update

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace PolymerEndpoint.Atomic

theorem theorem_4_9 {d : ℕ} (hd : 1 ≤ d) (𝔏 : Measure ℝ)
    [IsProbabilityMeasure 𝔏] (hdeg : Nondegenerate 𝔏)
    (β : ℝ) (hβ : 0 < β) (hmom : MomentCondition 𝔏 β)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Cell d → Ω → ℝ)
    (henv : IsEnvironment X 𝔏 P) :
    ∀ᵐ a ∂P, Tendsto
      (fun n : ℕ => Wdist (empirical X β n a) (M (d := d) 𝔏 β))
      atTop (𝓝 0) := by sorry

end PolymerEndpoint.Atomic
