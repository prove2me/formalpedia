-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullU_comp
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:15:11.431523+00:00
-- url     : https://prove2.me/theorems/54a5232d-f827-4f0f-bf3d-9bddb4673bfb
-- title:
--   DVR: pull U comp
-- statement:
--   The DVR construction uses the pull U comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L13-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/LBPull.lean#L13-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBPull
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
open ReciprocityTheory.ChartRestriction.G.Semi

theorem ReciprocityTheory.ChartRestriction.G.DVR.pullU_comp {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)ˣ) :
    pullU (f ≫ g) U x = pullU f (g ⁻¹ᵁ U) (pullU g U x) := by sorry
