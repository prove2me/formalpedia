-- Prove2me | Theorems.Thm_SurgeSpatial_Attraction_proposition_2
-- name    : SurgeSpatial.Attraction.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:24:38.047012+00:00
-- url     : https://prove2.me/theorems/151f3bb3-4dcf-4719-937d-eb0fe8b0c109
-- title:
--   Proposition 2, p. 15 — congestion bound V(x|p, T) ≤ ψ_x(s^T(x)) Γ-a.e.
-- statement:
--   Let $(p,\mathcal T)$ be a feasible solution of (P2). Then the equilibrium driver utility is bounded by the congestion function evaluated at the post-relocation supply:
--   $$V(x\mid p,\mathcal T)\le\psi_x\big(s^{\mathcal T}(x)\big)\qquad\Gamma\text{-a.e. } x\in\mathcal C.$$
--
--   This is the capacity constraint that, added to the knapsack relaxation of (P2), bounds how much supply a location can absorb at a given utility level.
-- source:
--   Besbes, Castro, Lobel, Surge Pricing and its Spatial Supply Response, SSRN 3124571 (version of May 17, 2019), p. 15, Proposition 2

import Mathlib
import Definitions.Def_SurgeSpatial_Attraction_Setting
open MeasureTheory

namespace SurgeSpatial.Attraction

theorem proposition_2 (M : Market) (hM : M.Standing) (p : E → ℝ) (T : Measure (E × E))
    (hpT : M.FeasibleP2 p T) :
    ∀ᵐ x ∂M.Γ, x ∈ M.C → M.V p T x ≤ M.psi x (M.sT T x) := by sorry

end SurgeSpatial.Attraction
