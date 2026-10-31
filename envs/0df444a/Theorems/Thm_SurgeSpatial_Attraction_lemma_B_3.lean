-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_lemma_B_3
-- name    : SurgeSpatial.Attraction.lemma_B_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:53.061403+00:00
-- url     : https://prove2.me/theorems/019c51ad-dff0-420e-bed0-e349cbdd49ad
-- title:
--   Lemma B-3, p. B-3 — a set of positive flow contains an indifferent pair
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2), and let $\mathcal L\subseteq\mathcal C\times\mathcal C$. If $\mathcal T(\mathcal L)>0$, then there is a pair $(x,y)\in\mathcal L$ with
--   $$y\in\mathcal{IR}(x\mid p,\mathcal T).$$
--
--   Any set of origin–destination pairs that carries flow contains a pair along which drivers are indifferent; it is the device by which "no indifferent pair" is turned into "no flow".
--
--   **Formalization Note** $\mathcal L$ need not be measurable; $\mathcal T(\mathcal L)$ is then the outer measure.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. B-3, Lemma B-3 (also Proposition 3(i), p. 16)

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem lemma_B_3 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) (L : Set (E × E)) (hL : L ⊆ M.C ×ˢ M.C) (hTL : 0 < T L) :
    ∃ q ∈ L, q.2 ∈ M.IR p T q.1 := by sorry

end SurgeSpatial.Attraction
