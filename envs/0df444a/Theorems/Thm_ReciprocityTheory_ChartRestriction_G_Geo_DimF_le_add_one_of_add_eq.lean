-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_DimF_le_add_one_of_add_eq
-- name    : ReciprocityTheory.ChartRestriction.G.Geo.DimF.le_add_one_of_add_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:23:44.64668+00:00
-- url     : https://prove2.me/theorems/8b2fc557-a130-48f4-ad04-36d4e084449b
-- title:
--   Dim F: le add one of add eq
-- statement:
--   The Dim F construction uses the le add one of add eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L209-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/InterDivSuppAB.lean#L209-L228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodA
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_IsCMOfIsRegularLocalRing
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_SaturatedChains_RingKrullDimLocalizationQuotientEqHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.DimF

theorem ReciprocityTheory.ChartRestriction.G.Geo.DimF.le_add_one_of_add_eq (a b D : WithBot ℕ∞) (x c : ℕ∞) (hx : x ≠ ⊤) (hc : c ≤ 1)
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (hD : D ≠ ⊤) (h1 : a + x = D) (h2 : b + ((x + c : ℕ∞) : WithBot ℕ∞) = D) :
    a ≤ b + 1 := by sorry
