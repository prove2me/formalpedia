-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_neg_7c4e4b03f070
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_neg_7c4e4b03f070
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:25:07.87416+00:00
-- url     : https://prove2.me/theorems/104bacdc-6b63-4daa-b447-3f3e3ac7161b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog neg 7c4e4b03f070: P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog neg 7c4e4b03f070
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog neg 7c4e4b03f070 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog neg 7c4e4b03f070 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L26-L29

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

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_neg_7c4e4b03f070 {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingFrac».«isMultiHomog_neg» := P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_neg_7c4e4b03f070
