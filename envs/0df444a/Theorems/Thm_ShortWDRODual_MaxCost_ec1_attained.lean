-- Prove2me | Theorems.Thm_ShortWDRODual_MaxCost_ec1_attained
-- name    : ShortWDRODual.MaxCost.ec1_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:25:45.037326+00:00
-- url     : https://prove2.me/theorems/92d585f9-424a-4d0e-8acd-8dbd3da37bf3
-- title:
--   Proof of Theorem 2, (EC.1), p. ec8 — on a Polish space, inf over Γ(ℙ̂, ℙ) of γ-ess sup c ≤ ρ is attained
-- statement:
--   Let $\mathcal X$ be a Polish space with its Borel $\sigma$-algebra, $\widehat{\mathbb P}$ and $\mathbb P$ probability measures on $\mathcal X$, $c:\mathcal X\times\mathcal X\to[0,\infty)$ continuous, and $\rho\ge0$. If
--   $$\inf_{\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)}\ \gamma\text{-}\operatorname*{ess\,sup}_{\widehat x,x\in\mathcal X}c(\widehat x,x)\le\rho,\tag{EC.1}$$
--   then there is a coupling $\gamma\in\Gamma(\widehat{\mathbb P},\mathbb P)$ with $\gamma\text{-}\operatorname*{ess\,sup}c\le\rho$, i.e. $c(\widehat x,x)\le\rho$ for $\gamma$-almost every $(\widehat x,x)$.
--
--   This is where the proof of Theorem 2 uses that $\mathcal X$ is Polish and $c$ continuous: it turns the inequality of the first chain into an equality. Remark 5 of the paper shows that without continuity of $c$ the duality can fail.
--
--   **Formalization Note** (EC.1) is `maxCost c Phat P ≤ ofReal ρ`, the infimum over couplings of the `essSup` of $\mathrm{ofReal}\circ c$, in $[0,\infty]$.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, proof of Theorem 2, (EC.1) and the following paragraph, p. ec8 (PDF p. 22)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting

namespace ShortWDRODual.MaxCost

open MeasureTheory ModelRiskOT.Duality
open scoped ENNReal

/-- Proof of Theorem 2 (p. ec8): on a Polish space with a continuous nonnegative cost, if
`inf_{γ ∈ Γ(ℙ̂, ℙ)} γ-ess sup c ≤ ρ` (EC.1), then some `γ ∈ Γ(ℙ̂, ℙ)` has `γ-ess sup c ≤ ρ`. -/
theorem ec1_attained {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat P : Measure X) [IsProbabilityMeasure Phat] [IsProbabilityMeasure P]
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hK : maxCost c Phat P ≤ ENNReal.ofReal ρ) :
    ∃ γ ∈ couplings Phat P,
      essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ := by sorry

end ShortWDRODual.MaxCost
