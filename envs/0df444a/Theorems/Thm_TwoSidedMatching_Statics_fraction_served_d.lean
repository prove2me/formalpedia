-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_fraction_served_d
-- name    : TwoSidedMatching.Statics.fraction_served_d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:47.775611+00:00
-- url     : https://prove2.me/theorems/3b837d94-dc41-485a-9826-cb73e31416c9
-- title:
--   Supplemental Note p. 15 — fraction of buyers served falls as buyer arrivals rise
-- statement:
--   Fix the seller arrival rate and the distributions. Let $\nu^*_d=\mu^*/(\lambda^dT)$ be the fraction of arriving buyers matched by the fluid optimum. If $0<\lambda^d_1\le\lambda^d_2$, then
--
--   $$\nu^*_d(\lambda^d_2,\lambda^s)\le\nu^*_d(\lambda^d_1,\lambda^s).$$
--
--   This fraction comparison is the step in the proof of Theorem 3 that controls the buyer price through the inverse survival function.
--
--   **Formalization Note** The printed proof writes strict inequality between rates. Equality is included because the paper defines increasing and decreasing in the weak sense. Density continuity is carried with the fluid model; the fraction comparison does not require nonnegative seller costs.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 15 (PDF 55), proof of Theorem 3, part (1), nu-star comparison

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Supplemental Note p. 15, proof of Theorem 3, part (1). -/
theorem fraction_served_d (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hT : 0 < T) :
    ∀ lamS lamD₁ lamD₂ : ℝ, 0 < lamS → 0 < lamD₁ → lamD₁ ≤ lamD₂ →
      nuStarD E lamD₂ lamS T ≤ nuStarD E lamD₁ lamS T := by sorry

end TwoSidedMatching.Statics
