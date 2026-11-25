-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_DimensionQuotientBound_local_step
-- name    : ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:59:12.446282+00:00
-- url     : https://prove2.me/theorems/e4c16004-7029-45fb-98b5-ed340a7131c9
-- title:
--   Dimension Quotient Bound: local step
-- statement:
--   The Dimension Quotient Bound construction uses the local step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L30-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/DimensionQuotientBound.lean#L30-L93

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

theorem ReciprocityTheory.ChartRestriction.G.T0.DimensionQuotientBound.local_step {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] (M : Ideal B) [hM : M.IsMaximal]
    (w e : B) (hw : w ∈ M) (hw0 : w ≠ 0) (he : e ≠ 0) :
    ∃ q : Ideal B, q.IsPrime ∧ q ≤ M ∧ e ∉ q ∧ w ∉ q ∧
      ∀ P : Ideal B, P.IsPrime → q ≤ P → P ≤ M → w ∈ P → P = M := by sorry
