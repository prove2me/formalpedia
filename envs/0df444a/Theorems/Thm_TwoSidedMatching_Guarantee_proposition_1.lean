-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_proposition_1
-- name    : TwoSidedMatching.Guarantee.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:07.958348+00:00
-- url     : https://prove2.me/theorems/c564940e-f8f4-4361-8af3-5c5a2ac2174c
-- title:
--   Proposition 1 — constant prices attain the fluid optimum
-- statement:
--   For regular continuous value densities, positive arrival rates and horizon, overlapping supports, and nonnegative support lower endpoints, μ* is the largest admissible volume with nonnegative marginal virtual surplus. Demand and supply at its inverse-distribution prices both equal μ*. The prices satisfy p* ≥ w*, and the constant trajectory (p*,w*) is feasible and optimal for (D):
--
--   $$\bar J^*=(p^*-w^*)\mu^*.$$
--
--   This identifies the fluid benchmark used in the guarantee.
--
--   **Formalization Note** Density continuity ensures attainment and valid inverses. Nonnegative support lower endpoints make these prices admissible in the paper's nonnegative price domain.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 16, Proposition 1, (1)–(3) (PDF p. 17)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

namespace TwoSidedMatching.Guarantee

/-- Main text Proposition 1, including attainment of the deterministic program. -/
theorem proposition_1 (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS ≤ E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    muStar E lamD lamS T ∈ admissibleVolume E lamD lamS T ∧
    lamD * T * FdBar E (pStar E lamD lamS T) = muStar E lamD lamS T ∧
    lamS * T * Fs E (wStar E lamD lamS T) = muStar E lamD lamS T ∧
    wStar E lamD lamS T ≤ pStar E lamD lamS T ∧
    IsFeasiblePath E lamD lamS T (fun _ => (pStar E lamD lamS T, wStar E lamD lamS T)) ∧
    fluidValue E lamD lamS T =
      fluidObjective E lamD lamS T (fun _ => (pStar E lamD lamS T, wStar E lamD lamS T)) ∧
    fluidValue E lamD lamS T =
      (pStar E lamD lamS T - wStar E lamD lamS T) * muStar E lamD lamS T := by sorry

end TwoSidedMatching.Guarantee
