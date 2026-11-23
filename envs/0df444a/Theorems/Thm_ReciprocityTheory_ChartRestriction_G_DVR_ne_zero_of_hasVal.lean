-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_ne_zero_of_hasVal
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.ne_zero_of_hasVal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:07.395394+00:00
-- url     : https://prove2.me/theorems/e3d923ca-e2ac-40b0-9019-bc1fab6a255d
-- title:
--   DVR: ne zero of has Val
-- statement:
--   The DVR construction uses the ne zero of has Val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L88-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalB.lean#L88-L94

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_WchartLePreimage
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalB
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

theorem ReciprocityTheory.ChartRestriction.G.DVR.ne_zero_of_hasVal {c : FractionRing V} {n : ℤ} (hϖ : Irreducible ϖ) (hn : HasVal ϖ c n) : c ≠ 0 := by sorry
