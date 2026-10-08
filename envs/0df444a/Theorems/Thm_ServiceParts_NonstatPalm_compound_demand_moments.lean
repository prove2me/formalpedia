-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_compound_demand_moments
-- name    : ServiceParts.NonstatPalm.compound_demand_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:35.35999+00:00
-- url     : https://prove2.me/theorems/94bc7240-e147-488b-bba9-3421003f5c43
-- title:
--   Section 9.2 — E[Y(t)] = m(t)E[Q] and Var[Y(t)] = m(t)E[Q²] for nonstationary compound Poisson demand
-- statement:
--   In the single-location model with nonstationary compound Poisson demand (orders with rate $\lambda$, mean function $m$, i.i.d. order sizes $Q \ge 1$ independent of the order process), let $Y(t)$ be the number of units demanded in $[0,t]$. For every $t \ge 0$:
--
--   1. $E[Y(t)] = m(t)\,E[Q]$ (as extended nonnegative numbers, so both sides may be $+\infty$);
--   2. if $E[Q^2] < \infty$, then $E[Y(t)^2] < \infty$ and
--   $$\operatorname{Var}[Y(t)] = m(t)\,E[Q^2].$$
--
--   These are the first two moments of the compound Poisson demand used by the book's approximations.
--
--   **Formalization Note** The book asserts both identities without stating that the moments of $Q$ are finite; the mean identity is stated in $[0,\infty]$, where it holds without assumption, and the variance identity under $E[Q^2] < \infty$, which is needed for the variance to be finite. $Q$ is represented by the size of the first order, all sizes being identically distributed.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, p. 218, Section 9.2

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_CompoundResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem compound_demand_moments {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : CompoundResupplySystem Ω P E)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (S.unitsDemanded t ω : ENNReal) ∂P =
        ENNReal.ofReal (S.meanFn t) * ∫⁻ ω, (S.size 0 ω : ENNReal) ∂P ∧
      (MemLp (fun ω => (S.size 0 ω : ℝ)) 2 P →
        MemLp (fun ω => (S.unitsDemanded t ω : ℝ)) 2 P ∧
          variance (fun ω => (S.unitsDemanded t ω : ℝ)) P =
            S.meanFn t * ∫ ω, (S.size 0 ω : ℝ) ^ 2 ∂P) := by sorry

end ServiceParts.NonstatPalm
