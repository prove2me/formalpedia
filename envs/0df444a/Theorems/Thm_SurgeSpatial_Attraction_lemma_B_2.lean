-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_B_2
-- name    : SurgeSpatial.Attraction.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:38.574991+00:00
-- url     : https://prove2.me/theorems/09191101-80a8-4a90-afdc-065aea781a12
-- title:
--   Lemma B-2, p. B-1 — indifference propagates along segments
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2), let $x\in\mathcal C$ and $y\in\mathcal{IR}(x\mid p,\mathcal T)$. Then
--   $$y\in\mathcal{IR}(w\mid p,\mathcal T)\qquad\text{for every } w\in[x,y],$$
--   the closed segment from $x$ to $y$.
--
--   If drivers from $x$ are willing to go to $y$, so are drivers from every point on the way.
--
--   **Formalization Note** The page writes the segment as $[x\wedge y,x\vee y]$ in the natural order of the segment, and names the intermediate point $z$; here it is `segment ℝ x y` and the point is $w$.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. B-1, Lemma B-2

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_B_2 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (x y : E) (hx : x ∈ M.C) (hy : y ∈ M.IR p T x) :
    ∀ w ∈ segment ℝ x y, y ∈ M.IR p T w := by sorry

end SurgeSpatial.Attraction
