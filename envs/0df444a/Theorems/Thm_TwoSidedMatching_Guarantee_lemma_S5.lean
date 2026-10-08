-- Prove2me | Theorems.Thm_TwoSidedMatching_Guarantee_lemma_S5
-- name    : TwoSidedMatching.Guarantee.lemma_S5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T10:19:22.837427+00:00
-- url     : https://prove2.me/theorems/0a26bfe2-c2cc-48ac-9786-9484b4f45e05
-- title:
--   Lemma S.5 — fluid volume and profit rise with either arrival rate
-- statement:
--   Increasing either buyer or seller arrival rate, while keeping the other rate, horizon and distributions fixed, weakly increases both the optimal trade volume and fluid profit. Thus all four comparisons hold:
--
--   $$\mu^*(\lambda^d_1,\lambda^s)\le\mu^*(\lambda^d_2,\lambda^s),\quad\bar J^*(\lambda^d_1,\lambda^s)\le\bar J^*(\lambda^d_2,\lambda^s)\quad(\lambda^d_1\le\lambda^d_2),$$
--   $$\mu^*(\lambda^d,\lambda^s_1)\le\mu^*(\lambda^d,\lambda^s_2),\quad\bar J^*(\lambda^d,\lambda^s_1)\le\bar J^*(\lambda^d,\lambda^s_2)\quad(\lambda^s_1\le\lambda^s_2).$$
--
--   It controls the scaled systems in Theorem 2.
--
--   **Formalization Note** All rates are positive. Density continuity and nonnegative support lower endpoints are standing assumptions.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 4, Lemma S.5 and proof pp. 4–5 (PDF pp. 44–45)

import Mathlib
import Definitions.Def_TwoSidedMatching_Guarantee_Market

namespace TwoSidedMatching.Guarantee

/-- Supplemental Note Lemma S.5: both the optimal volume and deterministic
profit increase with either arrival rate. -/
theorem lemma_S5 (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hgap : E.loS ≤ E.hiB)
    (hloB : 0 ≤ E.loB) (hloS : 0 ≤ E.loS) (hT : 0 < T) :
    (∀ lamD₁ lamD₂ lamS : ℝ, 0 < lamD₁ → lamD₁ ≤ lamD₂ → 0 < lamS →
      muStar E lamD₁ lamS T ≤ muStar E lamD₂ lamS T ∧
      fluidValue E lamD₁ lamS T ≤ fluidValue E lamD₂ lamS T) ∧
    (∀ lamS₁ lamS₂ lamD : ℝ, 0 < lamS₁ → lamS₁ ≤ lamS₂ → 0 < lamD →
      muStar E lamD lamS₁ T ≤ muStar E lamD lamS₂ T ∧
      fluidValue E lamD lamS₁ T ≤ fluidValue E lamD lamS₂ T) := by sorry

end TwoSidedMatching.Guarantee
