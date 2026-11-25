-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_isMultiHomog_add_08ecdd1ec297
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_isMultiHomog_add_08ecdd1ec297
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:34.233508+00:00
-- url     : https://prove2.me/theorems/272dc8bf-a0de-49a6-b250-c789acf48062
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Local is Multi Homog add 08ecdd1ec297: P2 M Ground Theory Heights  Heights Inter Loc Ring Local is Multi Homog add 08ecdd1ec297
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Local is Multi Homog add 08ecdd1ec297 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Local is Multi Homog add 08ecdd1ec297 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingLocal.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingLocal.lean#L19-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StLocRingFrac
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_AvoidRing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PLocRingLocal
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
open GroundTheory.Heights₂.Heights.Inter.LocRingLocal
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_isMultiHomog_add_08ecdd1ec297 {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingLocal».«isMultiHomog_add» := P2M_GroundTheory_Heights__Heights_Inter_LocRingLocal_isMultiHomog_add_08ecdd1ec297
