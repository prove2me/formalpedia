-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_1
-- name    : SurgeSpatial.Attraction.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:42.734994+00:00
-- url     : https://prove2.me/theorems/01544eae-95b7-430d-a2e7-8c7d9c5e35fa
-- title:
--   Lemma 1, p. 13 — the equilibrium utility V_B(·|p, T) is 1-Lipschitz
-- statement:
--   Let $B\subseteq\mathcal C$ be measurable with $\Gamma(B)>0$, let $p$ be a measurable price mapping on $B$ with $p\ge0$ on $B$, and let $\mathcal T\in\mathcal F(\Theta)$ be a feasible flow. Then the utility $x\mapsto V_B(x\mid p,\mathcal T)$ of drivers restricted to destinations in $B$ is 1-Lipschitz on $\mathcal C$:
--   $$|V_B(x\mid p,\mathcal T)-V_B(y\mid p,\mathcal T)|\le\|x-y\|\qquad x,y\in\mathcal C.$$
--
--   No equilibrium is assumed. This regularity underlies every later statement about indifference and attraction regions.
--
--   **Formalization Note** The price mapping is a function on $\mathbb R^2$ whose restriction to $B$ is measurable; values outside $B$ do not enter $V_B$. Standing assumptions of §3.1 are included.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. 13, Lemma 1

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_1 (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp : Measurable (B.domRestrict p))
    (hp0 : ∀ y ∈ B, 0 ≤ p y) (T : Measure (E × E)) (hT : M.FeasFlow T) :
    LipschitzOnWith 1 (M.VB B p T) M.C := by sorry

end SurgeSpatial.Attraction
