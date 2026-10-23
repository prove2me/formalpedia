-- Prove2me | Theorems.Thm_RepRegion_Density_lemma_6_1
-- name    : RepRegion.Density.lemma_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:05.743636+00:00
-- url     : https://prove2.me/theorems/c717881b-780c-43bb-be00-07dd000d9a49
-- title:
--   Lemma 6.1, p. 24 — the coverage region of a sample-covering method comes arbitrarily close to every point of a compact subset of the support
-- statement:
--   Let $(M, d)$ be a metric space whose closed balls are measurable and let $X_1, X_2, \dots$ be i.i.d. $M$-valued random variables with law $P_X$. Let $(\mathcal C, f)$ be a sample-covering RRS method and let $K$ be any compact subset of the support of $P_X$. Then
--   $$\sup\Bigl\{\inf\{d(x, z) : z \in C_n(f)\} : x \in K\Bigr\} \xrightarrow[n \to \infty]{\text{a.s.}} 0.$$
--
--   Every point of $K$ is eventually within any given distance of the coverage region. The lemma needs no regularity of the class of regions; it is the geometric step behind Theorem 6.2.
--
--   **Formalization Note.** The infimum is the extended distance `Metric.infEDist`, which is $+\infty$ to the empty set (the right value at $n = 0$), and the supremum is taken in $[0, \infty]$. The class $\mathcal C$ plays no role, so it is not a parameter.
-- source:
--   Estes, Ball & Lovell, Data Exploration by Representative Region Selection: Axioms and Convergence, SSRN preprint 3005997, p. 24, Lemma 6.1

import Mathlib
import Definitions.Def_RepRegion_Density_Model

open MeasureTheory ProbabilityTheory Filter Topology ENNReal

namespace RepRegion.Density

theorem lemma_6_1 {M Ω : Type*}
    [MetricSpace M] [MeasurableSpace M] [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → M)
    (hXm : ∀ i, Measurable (X i)) (hind : iIndepFun X P)
    (hid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hball : ∀ (x : M) (r : ℝ), MeasurableSet (Metric.closedBall x r))
    (f : Finset M → Finset (Set M)) (hcov : SampleCovering f)
    (K : Set M) (hKc : IsCompact K) (hKs : K ⊆ supp (P.map (X 0))) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ =>
      ⨆ x ∈ K, Metric.infEDist x (coverage f (sample X n ω))) atTop (𝓝 0) := by sorry

end RepRegion.Density
