-- Prove2me | Theorems.Thm_RepRegion_Density_corollary_6_2
-- name    : RepRegion.Density.corollary_6_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:57.86767+00:00
-- url     : https://prove2.me/theorems/2476495f-c69a-4e24-bac9-db04d26e6367
-- title:
--   Corollary 6.2, p. 25 — P_X(C_n(f)) → 1 a.s. when the support is compact
-- statement:
--   In the setting of Theorem 6.1, suppose that $P_X$ has compact support $K$ with $P_X(K) = 1$. Let $(\mathcal C, f)$ be a sample-covering RRS method whose regions come from a uniform-scale class $(\mathcal C, \Theta, R)$ that is uniformly continuous with respect to $P_X$. If $f$ has asymptotically-bounded cardinality, then
--   $$P_X\bigl(C_n(f)\bigr) \xrightarrow[n \to \infty]{\text{a.s.}} 1.$$
--
--   The coverage region eventually carries almost all of the probability. In the proof of the goal theorem this controls the part of the support where the density estimate is $0$.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 25, Corollary 6.2

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem corollary_6_2 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1)
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (f : Finset M → Finset (Set M)) (hf : IsRRSMethod C f) (hcov : SampleCovering f)
    (hcard : AsympBoundedCard P X f) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      P.map (X 0) (coverage f (sample X n ω))) atTop (𝓝 1) := by sorry

end RepRegion.Density
