-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_add_c9d375b6206a
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_add_c9d375b6206a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:23:11.640331+00:00
-- url     : https://prove2.me/theorems/a9e03102-45e0-44ac-8b65-8efb1776b3a5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog add c9d375b6206a: P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog add c9d375b6206a
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog add c9d375b6206a construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog add c9d375b6206a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L18-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingFrac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.LocRingFrac
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_add_c9d375b6206a {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingFrac».«isMultiHomog_add» := P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_add_c9d375b6206a
