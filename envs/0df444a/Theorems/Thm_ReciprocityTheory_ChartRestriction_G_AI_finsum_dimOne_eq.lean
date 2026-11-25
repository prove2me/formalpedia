-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_finsum_dimOne_eq
-- name    : ReciprocityTheory.ChartRestriction.G.AI.finsum_dimOne_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:48.341831+00:00
-- url     : https://prove2.me/theorems/cc7d514b-6cd5-40c7-a5c6-96bd5eb28517
-- title:
--   AI: finsum dim One eq
-- statement:
--   The AI construction uses the finsum dim One eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L265-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArithmeticIntersection/LengthCokerEqKerAddDimOneOrderSum.lean#L265-L268

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

theorem ReciprocityTheory.ChartRestriction.G.AI.finsum_dimOne_eq (hdim : ringKrullDim A = 1) (F : PrimeSpectrum A → ℕ∞) :
    ∑ᶠ (p : PrimeSpectrum A) (_ : ringKrullDim (A ⧸ p.asIdeal) = 1), F p =
      ∑ p ∈ (finite_dimOne hdim).toFinset, F p := by sorry
