-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_JGPf_comp_eq
-- name    : ReciprocityTheory.ChartRestriction.G.TB.JGPf.comp_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:40:06.887952+00:00
-- url     : https://prove2.me/theorems/fe77d649-40be-5a25-87b0-b4b1df473105
-- title:
--   JGPf: comp eq
-- statement:
--   The JGPf construction uses the comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/JetGlue.lean#L37-L39

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

theorem ReciprocityTheory.ChartRestriction.G.TB.JGPf.comp_eq {A B C D : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C) (f g : C ⟶ D) (h : v ≫ f = v ≫ g) :
    (u ≫ v) ≫ f = (u ≫ v) ≫ g := by sorry
