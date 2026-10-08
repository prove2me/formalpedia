-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_demand_count_mean
-- name    : ServiceParts.NonstatPalm.demand_count_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:56:34.205271+00:00
-- url     : https://prove2.me/theorems/76dbb29d-6bbc-401a-8b45-b2d0487a1565
-- title:
--   Section 9.1 — the expected number of demands through t is m(t) = ∫₀ᵗ λ(s) ds
-- statement:
--   In the single-location model with nonstationary Poisson demand of rate $\lambda(s) \ge 0$, let $N(t)$ be the number of demands in $[0,t]$. For every $t \ge 0$,
--   $$E\bigl[N(t)\bigr] = m(t) = \int_0^t \lambda(s)\,ds.$$
--
--   This identifies the mean function $m$ used throughout Chapter 9 as the expected number of demands.
--
--   **Formalization Note** The expectation is the lower Lebesgue integral of $N(t)$ as an extended nonnegative number, so the identity also asserts that $E[N(t)]$ is finite.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 215-216, Section 9.1

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem demand_count_mean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (S.demandCount t ω : ENNReal) ∂P = ENNReal.ofReal (∫ s in (0 : ℝ)..t, S.rate s) := by sorry

end ServiceParts.NonstatPalm
