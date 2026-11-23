-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_of_ne_zero
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasVal_of_ne_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:49:53.118054+00:00
-- url     : https://prove2.me/theorems/0edfe702-d857-46d1-9c60-8e6f835e9026
-- title:
--   DVR: has Val of ne zero
-- statement:
--   The DVR construction uses the has Val of ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L107-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L107-L124

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasVal_of_ne_zero (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : ∃ n, HasVal ϖ c n := by sorry
