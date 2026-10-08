-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_isClosed_attainableSet
-- name    : StochApproxDyn.Attractor.isClosed_attainableSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:46:02.674683+00:00
-- url     : https://prove2.me/theorems/a9b5637e-ae1b-44ae-9422-fcc78e5015d8
-- title:
--   Lemma 7.1 (closedness) — the set $\mathrm{Att}(X)$ of attainable points is closed
-- statement:
--   Let $\Phi$ be a semiflow on a metric space $M$ and let $X$ be a process on $(\Omega,\mathcal F,P)$ satisfying the standing assumptions of Section 7 (continuous paths, adapted to $(\mathcal F_t)$, condition (24) with a function $w(t,\delta,T)\downarrow0$). Then the set of attainable points
--   $$\mathrm{Att}(X)=\{p\in M:\ P(\exists s\ge t:\ X(s)\in U)>0\ \text{for every } t>0 \text{ and every open } U\ni p\}$$
--   is closed in $M$.
--
--   This is the first of the three assertions of Lemma 7.1.
--
--   **Formalization Note** The standing assumptions are those of the definition `SatisfiesStandingAssumption`; $P$ is a probability measure.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 31, Section 7.1, Lemma 7.1 (first assertion)

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- Lemma 7.1, first assertion (Benaïm 1999, p. 31): `Att(X)` is closed. -/
theorem isClosed_attainableSet {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0)
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    IsClosed (attainableSet P X) := by sorry

end StochApproxDyn.Attractor
