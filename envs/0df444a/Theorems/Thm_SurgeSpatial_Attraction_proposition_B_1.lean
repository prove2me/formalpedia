-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_proposition_B_1
-- name    : SurgeSpatial.Attraction.proposition_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:57.144352+00:00
-- url     : https://prove2.me/theorems/4ab32e84-1f2f-4cb0-b974-558a5a8e44bb
-- title:
--   Proposition B-1, p. B-2 — flow separation at the endpoints of an attraction region and at its sink
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2) and let $z\in\mathcal C$ be a sink, with attraction region $A=A(z\mid p,\mathcal T)$, endpoints $X_a=X_a(z\mid p,\mathcal T)$ and $\mathcal L=\bigcup_{a}\{X_a\}$. Write $A^c=\mathcal C\setminus A$. Then
--
--   1. no flow enters $A$ from outside, and no flow leaves the inner part of $A$ for the outside or the endpoints:
--   $$\mathcal T(A^c\times A)=0,\qquad \mathcal T\Big(\big(\{z\}\cup\textstyle\bigcup_{a}[z,X_a)\big)\times\big((A^c\cup\mathcal L)\setminus\{z\}\big)\Big)=0;$$
--   2. no flow crosses between different rays: for disjoint sets of directions $R_1,R_2$,
--   $$\mathcal T\Big(\textstyle\bigcup_{a\in R_1}(z,X_a]\times\bigcup_{a\in R_2}(z,X_a]\Big)=0.$$
--
--   This separation is what allows the flow inside an attraction region to be replaced without disturbing the rest of the city.
--
--   **Formalization Note** The printed second part of (i) has an unbalanced bracket, $\bigcup_a[z,X_a\times(\dots)$. The proof works with $A^\circ(z)\cup\{z\}=\{z\}\cup\bigcup_a(z,X_a)$, which is formalized here as $\{z\}\cup\bigcup_a[z,X_a)$ (half-open segments; this also covers $z$ when every $X_a=z$). The closed reading would forbid flow out of the endpoints, which Proposition B-2 allows. $[z,X_a)$ is `segment ℝ z X_a \ {X_a}` and $(z,X_a]$ is `segment ℝ z X_a \ {z}`.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. B-2, Proposition B-1

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem proposition_B_1 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z) :
    (T ((M.C \ M.attr p T z) ×ˢ M.attr p T z) = 0 ∧
      T (({z} ∪ ⋃ a : S1, (segment ℝ z (M.Xend p T z a) \ {M.Xend p T z a})) ×ˢ
          (((M.C \ M.attr p T z) ∪ Set.range (M.Xend p T z)) \ {z})) = 0) ∧
    (∀ R₁ R₂ : Set S1, Disjoint R₁ R₂ →
      T ((⋃ a ∈ R₁, (segment ℝ z (M.Xend p T z a) \ {z})) ×ˢ
          (⋃ a ∈ R₂, (segment ℝ z (M.Xend p T z a) \ {z}))) = 0) := by sorry

end SurgeSpatial.Attraction
