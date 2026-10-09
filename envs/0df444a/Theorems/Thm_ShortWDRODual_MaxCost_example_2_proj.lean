-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_example_2_proj
-- name    : ShortWDRODual.MaxCost.example_2_proj
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:24:59.834898+00:00
-- url     : https://prove2.me/theorems/2881a883-50d5-42b2-93e0-b4488b7dcba2
-- title:
--   Example 2 (Proj), p. 7 — on a Polish space with Borel σ-algebra, measurable projection (Proj) holds
-- statement:
--   Let $\mathcal X$ be a Polish space (complete separable metrizable) with its Borel $\sigma$-algebra $\mathcal F$, and let $\widehat{\mathbb P}$ be a probability measure on $\mathcal X$. Then the measurable projection condition (Proj) holds: for every Borel set $A\subset\mathcal X\times\mathcal X$ which is diagonally dominant (that is, $(\widehat x,x)\in A$ implies $(x,x)\in A$),
--   $$\mathrm{Proj}_{\widehat x}(A)=\{\widehat x\in\mathcal X:(\widehat x,x)\in A\text{ for some }x\in\mathcal X\}\in\mathcal F_{\widehat{\mathbb P}},$$
--   where $\mathcal F_{\widehat{\mathbb P}}$ is the completion of $\mathcal F$ under $\widehat{\mathbb P}$.
--
--   This is the first half of Example 2: together with (Sel) it makes the interchangeability principle available on every Polish space, which the proof of Theorem 2 uses.
--
--   **Formalization Note** "$\in\mathcal F_{\widehat{\mathbb P}}$" is `NullMeasurableSet` for $\widehat{\mathbb P}$. The projection is the image under the first coordinate map.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Example 2, p. 7 (PDF p. 7), first clause; (Proj) as defined in Proposition 1, p. 6

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Example 2 (p. 7), first clause: on a Polish space with its Borel σ-algebra, (Proj) holds
for every probability measure `ℙ̂`. -/
theorem example_2_proj {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat] :
    ShortWDRODual.IP.Proj Phat := by sorry

end ShortWDRODual.MaxCost
