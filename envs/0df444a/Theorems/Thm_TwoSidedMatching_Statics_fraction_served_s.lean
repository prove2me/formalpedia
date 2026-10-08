-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_fraction_served_s
-- name    : TwoSidedMatching.Statics.fraction_served_s
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:13.644337+00:00
-- url     : https://prove2.me/theorems/5bd530cb-b665-499a-8116-1c587559cfac
-- title:
--   Supplemental Note p. 15 — fraction of sellers served falls as seller arrivals rise
-- statement:
--   Fix the buyer arrival rate and the distributions. Let $\nu^*_s=\mu^*/(\lambda^sT)$ be the fraction of arriving sellers matched by the fluid optimum. If $0<\lambda^s_1\le\lambda^s_2$, then
--
--   $$\nu^*_s(\lambda^d,\lambda^s_2)\le\nu^*_s(\lambda^d,\lambda^s_1).$$
--
--   This fraction comparison is the step in the proof of Theorem 3 that controls the seller price through the inverse seller distribution function.
--
--   **Formalization Note** The printed proof writes strict inequality between rates. Equality is included because the paper defines increasing and decreasing in the weak sense. Density continuity is carried with the fluid model; the fraction comparison does not require nonnegative seller costs.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 15 (PDF 55), proof of Theorem 3, part (2), nu-star comparison

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Supplemental Note p. 15, proof of Theorem 3, part (2). -/
theorem fraction_served_s (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hT : 0 < T) :
    ∀ lamD lamS₁ lamS₂ : ℝ, 0 < lamD → 0 < lamS₁ → lamS₁ ≤ lamS₂ →
      nuStarS E lamD lamS₂ T ≤ nuStarS E lamD lamS₁ T := by sorry

end TwoSidedMatching.Statics
