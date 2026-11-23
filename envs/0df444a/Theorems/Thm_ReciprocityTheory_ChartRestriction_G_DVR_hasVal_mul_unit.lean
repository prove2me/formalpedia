-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasVal_mul_unit
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.hasVal_mul_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:23.409145+00:00
-- url     : https://prove2.me/theorems/f227a7b8-787b-487d-a840-ade8f6b59100
-- title:
--   DVR: has Val mul unit
-- statement:
--   The DVR construction uses the has Val mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L162-L167

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.hasVal_mul_unit {c : FractionRing V} {n : ℤ} (hn : HasVal ϖ c n) (v : Vˣ) :
    HasVal ϖ (c * algebraMap V (FractionRing V) (v : V)) n := by sorry
