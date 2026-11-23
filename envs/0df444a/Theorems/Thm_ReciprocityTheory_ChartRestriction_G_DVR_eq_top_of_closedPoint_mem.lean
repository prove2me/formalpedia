-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_eq_top_of_closedPoint_mem
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:47.664914+00:00
-- url     : https://prove2.me/theorems/19ad339d-34cd-4f29-bd1a-4d41b162e83a
-- title:
--   DVR: eq top of closed Point mem
-- statement:
--   The DVR construction uses the eq top of closed Point mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L50-L53

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.eq_top_of_closedPoint_mem {V : Type} [CommRing V] [IsLocalRing V] (U : (Spec (CommRingCat.of V)).Opens)
    (hU : (IsLocalRing.closedPoint V : Spec (CommRingCat.of V)) ∈ U) : U = ⊤ := by sorry
