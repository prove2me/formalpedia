-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_B_1
-- name    : SurgeSpatial.Attraction.lemma_B_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:39.700066+00:00
-- url     : https://prove2.me/theorems/339fadcb-8278-404a-bd8f-1a08866bcad6
-- title:
--   Lemma B-1, p. B-1 — an attraction region is closed, contains its sink, and is a union of segments [z, X_a]
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2) and let $z\in\mathcal C$ be a sink. Then $A(z\mid p,\mathcal T)$ is a closed set containing $z$; for every ray direction $a$, the part of $A(z)$ on $\{z\}\cup\{z+ta:t>0\}$ is the segment
--   $$A_a(z\mid p,\mathcal T)=[z,X_a(z\mid p,\mathcal T)],$$
--   and
--   $$A(z\mid p,\mathcal T)=\bigcup_{a\in R_z}A_a(z\mid p,\mathcal T).$$
--
--   Attraction regions are star-shaped around their sink, with one segment per ray; this is the geometry on which the construction of Theorem 1 is carried out.
--
--   **Formalization Note** Rays are indexed by unit vectors of $\mathbb R^2$; $A_a(z)$ includes $z$ itself.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. B-1, Lemma B-1

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_B_1 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (z : E) (hz : z ∈ M.C) (hsink : M.IsSink p T z) :
    IsClosed (M.attr p T z) ∧ z ∈ M.attr p T z ∧
      (∀ a : S1, M.attrRay p T z a = segment ℝ z (M.Xend p T z a)) ∧
      M.attr p T z = ⋃ a : S1, M.attrRay p T z a := by sorry

end SurgeSpatial.Attraction
