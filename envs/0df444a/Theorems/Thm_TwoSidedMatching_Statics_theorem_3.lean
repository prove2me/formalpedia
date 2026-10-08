-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_theorem_3
-- name    : TwoSidedMatching.Statics.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:28:03.353913+00:00
-- url     : https://prove2.me/theorems/6f51db43-e39e-4ae3-809e-34f0191b7387
-- title:
--   Theorem 3, main text p. 26 — market-size comparative statics of prices, matches, and fluid profit
-- statement:
--   Fix the buyer and seller distributions and a positive horizon. Let $p^*$ and $w^*$ be the fixed prices of Proposition 1, $\mu^*$ the fluid matched volume, and $\bar J^*$ the value of the fluid program (D).
--
--   1. If the buyer arrival rate rises while the seller rate stays fixed, both $p^*$ and $w^*$ weakly rise, and so do $\mu^*$ and $\bar J^*$.
--   2. If the seller arrival rate rises while the buyer rate stays fixed, both $p^*$ and $w^*$ weakly fall, while $\mu^*$ and $\bar J^*$ weakly rise.
--
--   In symbols, the demand-rate comparison includes
--
--   $$\lambda^d_1\le\lambda^d_2\quad\Longrightarrow\quad p^*(\lambda^d_1,\lambda^s)\le p^*(\lambda^d_2,\lambda^s),\quad w^*(\lambda^d_1,\lambda^s)\le w^*(\lambda^d_2,\lambda^s),$$
--
--   and analogous inequalities hold for the matched volume and fluid profit. The seller-rate comparison reverses the two price inequalities and preserves the other two.
--
--   This is the paper's principal fluid-market comparative-statics result.
--
--   **Formalization Note** Arrival rates and the horizon are strictly positive. Continuous densities and nonnegative seller support are disclosed standing conditions; the latter respects (D)'s nonnegative price paths. The fluid profit is the supremum over feasible paths, not a definition by the formula in Proposition 1.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), main text p. 26 (PDF 27), Theorem 3

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Theorem 3, main text p. 26: comparative statics of both optimal
fixed prices, matched volume and the value of the fluid program (D). -/
theorem theorem_3 (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hseller : 0 ≤ E.loS) (hT : 0 < T) :
    (∀ lamS lamD₁ lamD₂ : ℝ, 0 < lamS → 0 < lamD₁ → lamD₁ ≤ lamD₂ →
      pStar E lamD₁ lamS T ≤ pStar E lamD₂ lamS T ∧
      wStar E lamD₁ lamS T ≤ wStar E lamD₂ lamS T ∧
      muStar E lamD₁ lamS T ≤ muStar E lamD₂ lamS T ∧
      fluidValue E lamD₁ lamS T ≤ fluidValue E lamD₂ lamS T) ∧
    (∀ lamD lamS₁ lamS₂ : ℝ, 0 < lamD → 0 < lamS₁ → lamS₁ ≤ lamS₂ →
      pStar E lamD lamS₂ T ≤ pStar E lamD lamS₁ T ∧
      wStar E lamD lamS₂ T ≤ wStar E lamD lamS₁ T ∧
      muStar E lamD lamS₁ T ≤ muStar E lamD lamS₂ T ∧
      fluidValue E lamD lamS₁ T ≤ fluidValue E lamD lamS₂ T) := by sorry

end TwoSidedMatching.Statics
