-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_one_le_dim
-- name    : ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.one_le_dim
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:35:38.834535+00:00
-- url     : https://prove2.me/theorems/a055134d-41a5-5ebc-8a52-dd84f644a7e9
-- title:
--   Dimension Quotient Bound: one le dim
-- statement:
--   The Dimension Quotient Bound construction uses the one le dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L21-L28

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AvPrimeDimOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_DimensionQuotientBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.one_le_dim {R : Type*} [CommRing R] (p m : Ideal R) [p.IsPrime] [m.IsPrime] (h : p < m) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim R := by sorry
