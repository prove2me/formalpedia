-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_A_1
-- name    : SurgeSpatial.Attraction.lemma_A_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:35.090845+00:00
-- url     : https://prove2.me/theorems/ef91505b-6e35-422a-8d2a-4b73b2378565
-- title:
--   Lemma A-1, p. A-1 — V_B(·|p, T) lies in [−H, αV̄], and V ≥ 0 on the support of Γ
-- statement:
--   Let $B\subseteq\mathcal C$ be measurable with $\Gamma(B)>0$, let $p$ be measurable on $B$ with $p\ge0$ on $B$, and let $\mathcal T\in\mathcal F(\Theta)$. Write $H=\max_{x,y\in\mathcal C}\|x-y\|$ for the diameter of the city. Then
--
--   1. $V_B(x\mid p,\mathcal T)\in[-H,\ \alpha\bar V]$ for every $x\in\mathcal C$;
--   2. if moreover $p\ge0$ on all of $\mathcal C$, then $V(x\mid p,\mathcal T)\ge0$ for every $x\in\operatorname{supp}(\Gamma)$.
--
--   The bounds show that the essential suprema of the model are finite, so they can be subtracted and compared.
--
--   **Formalization Note** $H$ is `Metric.diam C` ($\mathcal C$ is compact). The second part concerns $V=V_{\mathcal C}$, which uses the prices on all of $\mathcal C$; the page states $p\ge0$ only on $B$, and the proof uses $U\ge0$ on $\mathcal C$, so the second part carries $p\ge0$ on $\mathcal C$ as its hypothesis. The support is Mathlib's `Measure.support` (every neighbourhood has positive measure).
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. A-1, Lemma A-1

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_A_1 (M : Market) (hM : M.Standing) (B : Set E) (hB : MeasurableSet B)
    (hBC : B ⊆ M.C) (hΓB : 0 < M.Γ B) (p : E → ℝ) (hp : Measurable (B.domRestrict p))
    (hp0 : ∀ y ∈ B, 0 ≤ p y) (T : Measure (E × E)) (hT : M.FeasFlow T) :
    (∀ x ∈ M.C, M.VB B p T x ∈ Set.Icc (-Metric.diam M.C) (M.α * M.Vbar)) ∧
      ((∀ y ∈ M.C, 0 ≤ p y) → ∀ x ∈ M.Γ.support, 0 ≤ M.V p T x) := by sorry

end SurgeSpatial.Attraction
