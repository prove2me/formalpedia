-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_sum_places_restrict
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_places_restrict
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:23:39.580307+00:00
-- url     : https://prove2.me/theorems/e636cc1b-a832-43a9-a394-ab1b7a2a0800
-- title:
--   Free Quotient Rank: sum places restrict
-- statement:
--   The Free Quotient Rank construction uses the sum places restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L31-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L31-L49

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_places_restrict (g : (K →+* ℂ) → ℝ) (hg : ∀ τ, g ((starRingEnd ℂ).comp τ) = g τ) :
    ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * g (σ.embedding.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by sorry
