-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_attainableSet_isPositivelyInvariant
-- name    : StochApproxDyn.Attractor.attainableSet_isPositivelyInvariant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T16:46:18.864614+00:00
-- url     : https://prove2.me/theorems/ddcc0aa6-3274-4627-aa0a-e212ea4afb43
-- title:
--   Lemma 7.1 (positive invariance) — $\Phi_t(\mathrm{Att}(X))\subset\mathrm{Att}(X)$ for all $t\ge0$
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$ and let $X$ be a process on $(\Omega,\mathcal F,P)$ satisfying the standing assumptions of Section 7 (continuous paths, adapted to $(\mathcal F_t)$, condition (24) with a function $w(t,\delta,T)\downarrow0$). Then the set $\mathrm{Att}(X)$ of attainable points is positively invariant under $\Phi$:
--   $$\Phi_t\big(\mathrm{Att}(X)\big)\subset\mathrm{Att}(X)\qquad\text{for all } t\ge0 .$$
--
--   This is the second assertion of Lemma 7.1: if the process can come close to $p$ at arbitrarily late times with positive probability, it can also come close to $\Phi_t(p)$, because condition (24) makes it follow the flow for a time $t$ with high conditional probability.
--
--   **Formalization Note** The standing assumptions are those of the definition `SatisfiesStandingAssumption`; $P$ is a probability measure.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 31, Section 7.1, Lemma 7.1 (second assertion)

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- Lemma 7.1, second assertion (Benaïm 1999, p. 31): `Att(X)` is positively invariant under `Φ`. -/
theorem attainableSet_isPositivelyInvariant {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsPositivelyInvariant Φ (attainableSet P X) := by sorry

end StochApproxDyn.Attractor
