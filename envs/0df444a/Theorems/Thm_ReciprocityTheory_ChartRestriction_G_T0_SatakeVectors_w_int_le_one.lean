-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_w_int_le_one
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.w_int_le_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:42:44.179373+00:00
-- url     : https://prove2.me/theorems/92287e9f-5c37-57d1-8d89-fba3474e75bb
-- title:
--   Satake Vectors: w int le one
-- statement:
--   The Satake Vectors construction uses the w int le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ExistsIntMultiple.lean#L89-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.w_int_le_one (w : FinitePlace K) (y : 𝓞 K) : w (y : K) ≤ 1 := by sorry
