-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_proposition_1
-- name    : TwoSidedMatching.Statics.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:27.585994+00:00
-- url     : https://prove2.me/theorems/2aec6b97-e873-4ed1-9fd1-0a41c77d1877
-- title:
--   Proposition 1, main text p. 16 — fixed prices solve the deterministic program
-- statement:
--   Let the buyer valuation and seller cost distributions have continuous, positive densities and increasing virtual value and cost. Let $\lambda^d,\lambda^s,T>0$ and suppose the lowest seller cost does not exceed the highest buyer valuation. Then the largest volume with nonnegative virtual surplus is attained. Its inverse-quantile prices $p^*$ and $w^*$ lie in their supports and satisfy
--
--   $$\lambda^d T\bar F^d(p^*)=\lambda^s T F^s(w^*)=\mu^*,\qquad w^*\le p^*.$$
--
--   The constant path $(p^*,w^*)$ is feasible and optimal for the fluid program (D), and its value obeys
--
--   $$\bar J^*=(p^*-w^*)\mu^*.$$
--
--   This identifies the prices and matched volume used by the market-size comparison.
--
--   **Formalization Note** Density continuity is an added regularity condition needed for attainment and inverse quantiles. The seller support is nonnegative so the constant seller price belongs to (D)'s nonnegative path class. The fluid value remains defined by the independent optimization problem (D).
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 16 (PDF 17), Proposition 1 and (1)–(3)

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Proposition 1, main text p. 16: the fixed prices solve (D), obey
the market-clearing and virtual-surplus conditions, and yield (3). -/
theorem proposition_1 (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hseller : 0 ≤ E.loS)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    IsGreatest {μ : ℝ | μ ∈ Set.Icc 0 (min (lamD * T) (lamS * T)) ∧
      0 ≤ V E lamD lamS T μ} (muStar E lamD lamS T) ∧
    pStar E lamD lamS T ∈ Set.Icc E.loB E.hiB ∧
    wStar E lamD lamS T ∈ Set.Icc E.loS E.hiS ∧
    lamD * T * FdBar E (pStar E lamD lamS T) = muStar E lamD lamS T ∧
    lamS * T * Fs E (wStar E lamD lamS T) = muStar E lamD lamS T ∧
    wStar E lamD lamS T ≤ pStar E lamD lamS T ∧
    IsFeasiblePath E lamD lamS T (fun _ => (pStar E lamD lamS T, wStar E lamD lamS T)) ∧
    (∀ π, IsFeasiblePath E lamD lamS T π →
      fluidObjective E lamD lamS T π ≤
        fluidObjective E lamD lamS T (fun _ => (pStar E lamD lamS T, wStar E lamD lamS T))) ∧
    fluidValue E lamD lamS T =
      (pStar E lamD lamS T - wStar E lamD lamS T) * muStar E lamD lamS T := by sorry

end TwoSidedMatching.Statics
