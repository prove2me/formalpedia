-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FreeQuotientRank_LocalQuotientRank_rank_quot
-- name    : ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.rank_quot
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T10:22:43.377928+00:00
-- url     : https://prove2.me/theorems/89d2ef35-be88-4380-8ba4-fc2ffa534f20
-- title:
--   Local Quotient Rank: rank quot
-- statement:
--   The Local Quotient Rank construction uses the rank quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalQuotientRank.lean#L13-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/Rationality/LocalQuotientRank.lean#L13-L48

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_FreeQuotPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_LocalQuotientRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FreeQuotientRank ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank
open NumberField Module
open scoped TensorProduct
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.LocalQuotientRank.rank_quot (M₁ : Submodule R X) (hM₁ : M₁.FG) (N : Submodule F X) :
    Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
        Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
      Module.finrank F ↥(Submodule.span F (M₁ : Set X)) := by sorry
