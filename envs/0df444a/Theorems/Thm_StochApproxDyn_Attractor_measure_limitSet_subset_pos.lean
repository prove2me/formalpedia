-- Prove2me | Theorems.Thm_StochApproxDyn_Attractor_measure_limitSet_subset_pos
-- name    : StochApproxDyn.Attractor.measure_limitSet_subset_pos
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:46:29.060065+00:00
-- url     : https://prove2.me/theorems/376200c5-7a40-4686-8eaa-0ea8e4a74554
-- title:
--   Theorem 7.3 — if $\mathrm{Att}(X)\cap B(A)\neq\emptyset$ then $P(L(X)\subset A)>0$
-- statement:
--   Let $\Phi$ be a semiflow on a **locally compact** metric space $M$, and let $X$ be a process on a probability space $(\Omega,\mathcal F,P)$ satisfying the standing assumptions of Section 7: continuous paths in $M$, adapted to a filtration $(\mathcal F_t)_{t\ge0}$, and for all $\delta>0$, $T>0$, $t\ge0$
--   $$P\Big(\sup_{s\ge t}\sup_{0\le h\le T}d\big(X(s+h),\Phi_h(X(s))\big)\ge\delta\ \Big|\ \mathcal F_t\Big)\le w(t,\delta,T)$$
--   with $w(t,\delta,T)\downarrow0$ as $t\to\infty$. Let $A\subset M$ be an attractor of $\Phi$ with basin $B(A)$. If some point of the basin is attainable by $X$, i.e. $\mathrm{Att}(X)\cap B(A)\neq\emptyset$, then
--   $$P\big(L(X)\subset A\big)>0 .$$
--
--   This is the main result of Section 7: a stochastic approximation process converges to a given attractor with positive probability as soon as it can reach the attractor's basin. It complements the almost sure limit set theorem, which says only that $L(X)$ is internally chain transitive.
--
--   **Formalization Note** The standing assumptions are the definition `SatisfiesStandingAssumption` (continuous paths only; the paper also allows càdlàg paths). The event $\{L(X)\subset A\}$ is measured by $P$ as an outer measure, so the statement needs no measurability hypothesis for it.
-- source:
--   Benaïm, Dynamics of Stochastic Approximation Algorithms, Séminaire de Probabilités XXXIII, LNM 1709 (1999), p. 31, Section 7.1, Theorem 7.3 (first statement)

import Mathlib
import Definitions.Def_StochApproxDyn_Attractor_Dynamics
import Definitions.Def_StochApproxDyn_Attractor_Process

open scoped NNReal ENNReal
open MeasureTheory

namespace StochApproxDyn.Attractor

/-- Theorem 7.3, first statement (Benaïm 1999, p. 31): if `M` is locally compact, `A` is an
attractor of `Φ` and `Att(X) ∩ B(A) ≠ ∅`, then `P(L(X) ⊆ A) > 0`. -/
theorem measure_limitSet_subset_pos {Ω M : Type*} {m0 : MeasurableSpace Ω} [MetricSpace M]
    [LocallyCompactSpace M] [MeasurableSpace M] [BorelSpace M] (Φ : Flow ℝ≥0 M) (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 m0) (X : ℝ≥0 → Ω → M)
    (w : ℝ≥0 → ℝ≥0 → ℝ≥0 → ℝ≥0) (hX : SatisfiesStandingAssumption Φ P ℱ X w) (A : Set M)
    (hA : StochApproxDyn.LimitSet.IsAttractor Φ A) (hAtt : (attainableSet P X ∩ StochApproxDyn.LimitSet.basin Φ A).Nonempty) :
    0 < P {ω | StochApproxDyn.LimitSet.limitSet (fun t => X t ω) ⊆ A} := by sorry

end StochApproxDyn.Attractor
