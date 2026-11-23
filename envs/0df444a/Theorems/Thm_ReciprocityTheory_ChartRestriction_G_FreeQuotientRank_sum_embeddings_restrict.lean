-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_sum_embeddings_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:23:31.161799+00:00
-- url     : https://prove2.me/theorems/57ede2ca-50b6-4b7d-9852-87e7a8a206f8
-- title:
--   Free Quotient Rank: sum embeddings restrict
-- statement:
--   The Free Quotient Rank construction uses the sum embeddings restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L13-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L13-L29

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_GlobQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreGlobPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open NumberField IsDedekindDomain
open scoped TensorProduct
variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict (g : (K →+* ℂ) → ℝ) :
    ∑ φ : K₁ →+* ℂ, g (φ.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by sorry
