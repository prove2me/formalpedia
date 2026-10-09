-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_example_2_sel
-- name    : ShortWDRODual.MaxCost.example_2_sel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:27:25.99165+00:00
-- url     : https://prove2.me/theorems/d1afe78d-7eef-4ef1-a9a2-9d4db727394e
-- title:
--   Example 2 (Sel), p. 7 — on a Polish space with Borel σ-algebra, measurable selection (Sel) holds
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra $\mathcal F$, and let $\widehat{\mathbb P}$ be a probability measure on $\mathcal X$, with $\mathcal F_{\widehat{\mathbb P}}$ the completion of $\mathcal F$ under $\widehat{\mathbb P}$. Then the measurable selection condition (Sel) holds: for every set-valued map $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ whose graph
--   $$\mathrm{Graph}(E)=\{(\widehat x,x)\in\mathcal X\times\mathcal X:x\in E(\widehat x)\}$$
--   is a Borel subset of $\mathcal X\times\mathcal X$, there is an $(\mathcal F_{\widehat{\mathbb P}},\mathcal F)$-measurable map $T:\mathcal X\to\mathcal X$ with $T(\widehat x)\in E(\widehat x)$ for every $\widehat x\in\mathcal X$.
--
--   This is the second half of Example 2. (Sel) is stronger than the weak selection condition (Sel\*) of Proposition 1, so with (Proj) it yields the interchangeability principle on Polish spaces.
--
--   **Formalization Note** "$E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$" is encoded as: every $E(\widehat x)$ is a nonempty measurable set. $(\mathcal F_{\widehat{\mathbb P}},\mathcal F)$-measurability of $T$ is `NullMeasurable T` for $\widehat{\mathbb P}$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, Example 2, p. 7 (PDF p. 7), second clause; (Sel) as defined in Remark 4, p. 7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Example 2 (p. 7), second clause: on a Polish space with its Borel σ-algebra, (Sel) holds
for every probability measure `ℙ̂`. -/
theorem example_2_sel {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat] :
    Sel Phat := by sorry

end ShortWDRODual.MaxCost
