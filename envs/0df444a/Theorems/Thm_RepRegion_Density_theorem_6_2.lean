-- Prove2me | Theorems.Thm_RepRegion_Density_theorem_6_2
-- name    : RepRegion.Density.theorem_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:02.08539+00:00
-- url     : https://prove2.me/theorems/e55c62ad-93af-4f8f-9a53-1c43afeefa46
-- title:
--   Theorem 6.2, p. 24 — with asymptotically bounded cardinality, P_X(K \ C_n(f)) → 0 a.s. for every compact K in the support
-- statement:
--   In the setting of Theorem 6.1, let $(\mathcal C, f)$ be a sample-covering RRS method whose regions come from a uniform-scale class $(\mathcal C, \Theta, R)$ that is uniformly continuous with respect to $P_X$. If $(\mathcal C, f)$ has asymptotically-bounded cardinality, then for every compact set $K$ contained in the support of $P_X$,
--   $$P_X\bigl(K \setminus C_n(f)\bigr) \xrightarrow[n \to \infty]{\text{a.s.}} 0.$$
--
--   The probability of an observation that lies in $K$ but outside the representatives' coverage region vanishes. With $K$ the whole support this becomes Corollary 6.2.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 24, Theorem 6.2

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem theorem_6_2 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (f : Finset M → Finset (Set M)) (hf : IsRRSMethod C f) (hcov : SampleCovering f)
    (hcard : AsympBoundedCard P X f) :
    ∀ K : Set M, IsCompact K → K ⊆ supp (P.map (X 0)) →
      ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
        P.map (X 0) (K \ coverage f (sample X n ω))) atTop (𝓝 0) := by sorry

end RepRegion.Density
