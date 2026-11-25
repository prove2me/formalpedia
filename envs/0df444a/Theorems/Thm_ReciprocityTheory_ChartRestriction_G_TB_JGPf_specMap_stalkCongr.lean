-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_specMap_stalkCongr
-- name    : ReciprocityTheory.ChartRestriction.G.TB.JGPf.specMap_stalkCongr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:19.546264+00:00
-- url     : https://prove2.me/theorems/9e5acdd7-d10c-49df-85f4-cca23a5b1acc
-- title:
--   JGPf: spec Map stalk Congr
-- statement:
--   The JGPf construction uses the spec Map stalk Congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L13-L16

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

theorem ReciprocityTheory.ChartRestriction.G.TB.JGPf.specMap_stalkCongr {X : Scheme.{u}} {x y : X} (e : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by sorry
