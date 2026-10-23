-- Prove2me | Theorems.Thm_RepRegion_Density_corollary_6_1
-- name    : RepRegion.Density.corollary_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:06.564252+00:00
-- url     : https://prove2.me/theorems/e721daa0-76e2-42c9-aa8d-db3393ca0255
-- title:
--   Corollary 6.1, p. 24 — proportions in the chosen regions converge uniformly to their probabilities
-- statement:
--   In the setting of Theorem 6.1, let $(\mathcal C, f)$ be an RRS method whose regions come from a uniform-scale class $(\mathcal C, \Theta, R)$ that is uniformly continuous with respect to $P_X$. If $P_X$ has compact support $K$ with $P_X(K) = 1$, then
--   $$\sup_{A \in f(S_n)} \bigl|\hat P_{X,n}(A) - P_X(A)\bigr| \xrightarrow[n \to \infty]{\text{a.s.}} 0.$$
--
--   The regions an RRS method chooses depend on the sample and need not converge to anything; the corollary says the observed proportions in them are nevertheless uniformly accurate. It is the first ingredient of the density-estimation results.
--
--   **Formalization Note.** The supremum is taken in $[0, \infty]$ (it is $0$ when $f(S_n)$ is empty). Uniform continuity uses the small-scale convention described in Theorem 6.1.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 24, Corollary 6.1

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem corollary_6_1 {M Ω Θ : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (C : Set (Set M)) (R : Θ → ℝ → Set M)
    (hUS : UniformScale C R) (hUC : UnifContWrt C R (P.map (X 0)))
    (K : Set M) (hK : K = supp (P.map (X 0))) (hKc : IsCompact K)
    (hK1 : P.map (X 0) K = 1)
    (f : Finset M → Finset (Set M)) (hf : IsRRSMethod C f) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      ⨆ A ∈ f (sample X n ω), ENNReal.ofReal |empFreq X n ω A - (P.map (X 0) A).toReal|)
      atTop (𝓝 0) := by sorry

end RepRegion.Density
