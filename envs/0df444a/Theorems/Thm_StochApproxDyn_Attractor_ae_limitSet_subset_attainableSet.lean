-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_ae_limitSet_subset_attainableSet
-- name    : StochApproxDyn.Attractor.ae_limitSet_subset_attainableSet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:46:17.085626+00:00
-- url     : https://prove2.me/theorems/d753f186-e90e-4a60-b4f2-442f9690a5d9
-- title:
--   Lemma 7.1 (almost sure containment) — $L(X)\subset\mathrm{Att}(X)$ almost surely ($M$ separable)
-- statement:
--   Let $\Phi$ be a semiflow on a **separable** metric space $M$ and let $X$ be a process on $(\Omega,\mathcal F,P)$ satisfying the standing assumptions of Section 7 (continuous paths, adapted to $(\mathcal F_t)$, condition (24) with a function $w(t,\delta,T)\downarrow0$). Then for $P$-almost every $\omega$, the limit set of the path $t\mapsto X(t)(\omega)$ is contained in the set of attainable points:
--   $$L(X)(\omega)\subset\mathrm{Att}(X)\qquad P\text{-a.s.}$$
--
--   This is the third assertion of Lemma 7.1: the process accumulates only at points it reaches with positive probability at arbitrarily late times.
--
--   **Formalization Note** Separability of $M$ (`SecondCountableTopology M`) is **added** to the paper's hypotheses. The paper's proof covers $M\setminus\mathrm{Att}(X)$ by open sets that the process eventually avoids almost surely and needs countably many of them. Without separability the assertion fails in models of set theory with a real-valued measurable cardinal (take $M$ uncountable and discrete, and $X(t)(\omega)=\omega$), so it cannot be proved in Lean's foundations. The paper's applications take $M\subset\mathbb R^m$.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 31, Section 7.1, Lemma 7.1 (third assertion)

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- Lemma 7.1, third assertion (Benaïm 1999, p. 31): almost surely `L(X) ⊆ Att(X)`. The
separability of `M` (`SecondCountableTopology M`) is an added hypothesis. -/
theorem ae_limitSet_subset_attainableSet {Ω M : Type*} {m0 : MeasurableSpace Ω}
    [MetricSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
    (Φ : Flow ℝ≥0 M) (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0)
    (X : ℝ≥0 → Ω → M) (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0)
    (hX : SatisfiesStandingAssumption Φ P ℱ X w) :
    ∀ᵐ ω ∂P, StochApproxDyn.LimitSet.limitSet (fun t => X t ω) ⊆ attainableSet P X := by sorry

end StochApproxDyn.Attractor
