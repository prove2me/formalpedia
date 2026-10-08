-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_lemma_S_5
-- name    : TwoSidedMatching.Statics.lemma_S_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:45.720887+00:00
-- url     : https://prove2.me/theorems/ef6d8a77-cccd-4f2d-8c50-29bab5c1da48
-- title:
--   Lemma S.5, Supplemental Note p. 4 — matches and fluid profit rise with either arrival rate
-- statement:
--   Hold the distributions and horizon fixed. When either positive arrival rate rises while the other stays fixed, both the optimally matched volume $\mu^*$ and the value $\bar J^*$ of the fluid program (D) weakly rise. For instance, if $0<\lambda^d_1\le\lambda^d_2$, then
--
--   $$\mu^*(\lambda^d_1,\lambda^s)\le\mu^*(\lambda^d_2,\lambda^s),\qquad \bar J^*(\lambda^d_1,\lambda^s)\le\bar J^*(\lambda^d_2,\lambda^s),$$
--
--   with corresponding inequalities for $0<\lambda^s_1\le\lambda^s_2$ at fixed demand rate.
--
--   The result supplies the quantity and profit clauses of Theorem 3.
--
--   **Formalization Note** The source's word “respectively” is read through the two parts of its proof: each part establishes both monotonicities for one rate. The fluid value is the optimum of (D), and density continuity and nonnegative seller support are the disclosed standing conditions.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note pp. 4–5 (PDF 44–45), Lemma S.5

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Lemma S.5, Supplemental Note p. 4, read with its two-part proof on pp. 4–5. -/
theorem lemma_S_5 (E : Environment) (T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hseller : 0 ≤ E.loS) (hT : 0 < T) :
    (∀ lamS lamD₁ lamD₂ : ℝ, 0 < lamS → 0 < lamD₁ → lamD₁ ≤ lamD₂ →
      muStar E lamD₁ lamS T ≤ muStar E lamD₂ lamS T ∧
      fluidValue E lamD₁ lamS T ≤ fluidValue E lamD₂ lamS T) ∧
    (∀ lamD lamS₁ lamS₂ : ℝ, 0 < lamD → 0 < lamS₁ → lamS₁ ≤ lamS₂ →
      muStar E lamD lamS₁ T ≤ muStar E lamD lamS₂ T ∧
      fluidValue E lamD lamS₁ T ≤ fluidValue E lamD lamS₂ T) := by sorry

end TwoSidedMatching.Statics
