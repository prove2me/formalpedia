-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_isGen_iff_isGenW
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.isGen_iff_isGenW
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:12:41.553829+00:00
-- url     : https://prove2.me/theorems/b5bcf3b0-7abb-41a0-ace6-edcdc2ee70c0
-- title:
--   DVR: is Gen iff is Gen W
-- statement:
--   The DVR construction uses the is Gen iff is Gen W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L28-L29

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.isGen_iff_isGenW {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L ψ ε)) : t.IsGen ↔ IsGenW L ψ ε t.s := by sorry
