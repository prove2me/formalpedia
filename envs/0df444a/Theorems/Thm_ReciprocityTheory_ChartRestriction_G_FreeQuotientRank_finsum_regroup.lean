-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_finsum_regroup
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finsum_regroup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:22:10.710811+00:00
-- url     : https://prove2.me/theorems/96e4bb95-967c-433a-ac61-91923c63cc48
-- title:
--   Free Quotient Rank: finsum regroup
-- statement:
--   The Free Quotient Rank construction uses the finsum regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L81-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/QCoreGlobPf.lean#L81-L123

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

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.finsum_regroup (F : HeightOneSpectrum (𝓞 K₁) → ℝ) (hF : (Function.support F).Finite) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K),
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la =
      ∑ᶠ w, F w * logN w := by sorry
