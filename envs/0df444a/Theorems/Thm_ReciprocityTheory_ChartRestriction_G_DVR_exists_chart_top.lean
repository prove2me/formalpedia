-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_exists_chart_top
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.exists_chart_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:28:03.982992+00:00
-- url     : https://prove2.me/theorems/95da43cd-7952-4681-a319-d7476e272f54
-- title:
--   DVR: exists chart top
-- statement:
--   The DVR construction uses the exists chart top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L94-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBLocalC.lean#L94-L103

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.exists_chart_top {V : Type} [CommRing V] [IsLocalRing V] {X : Scheme.{0}} (L : LB X) (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : K → (Spec (CommRingCat.of V) ⟶ X)) (ε : K → ℤ) :
    ∃ j₀ : K → L.ι, LB.wchart L φ j₀ = ⊤ := by sorry
