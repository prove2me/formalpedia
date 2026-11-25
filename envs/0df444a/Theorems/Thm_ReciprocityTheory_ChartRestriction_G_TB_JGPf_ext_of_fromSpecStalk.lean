-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_ext_of_fromSpecStalk
-- name    : ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:26.981473+00:00
-- url     : https://prove2.me/theorems/eb886f0f-4720-4dcc-be22-abb1b6bc1332
-- title:
--   JGPf: ext of from Spec Stalk
-- statement:
--   The JGPf construction uses the ext of from Spec Stalk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L20-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L20-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_JetGlue
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_JetGlue
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
open AlgebraicGeometry CategoryTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.JGPf
universe u
set_option maxHeartbeats 1000000

theorem ReciprocityTheory.ChartRestriction.G.TB.JGPf.ext_of_fromSpecStalk {Y X : Scheme.{u}} (f g : Y ⟶ X)
    (h : ∀ y, Y.fromSpecStalk y ≫ f = Y.fromSpecStalk y ≫ g) : f = g := by sorry
