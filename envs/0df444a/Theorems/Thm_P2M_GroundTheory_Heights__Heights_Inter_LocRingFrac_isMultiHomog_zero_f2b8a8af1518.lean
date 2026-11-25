-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_zero_f2b8a8af1518
-- name    : P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_zero_f2b8a8af1518
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:41:44.814976+00:00
-- url     : https://prove2.me/theorems/c9416a04-4182-4b37-92be-c35d7ebe2120
-- title:
--   P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog zero f2b8a8af1518: P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog zero f2b8a8af1518
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog zero f2b8a8af1518 construction uses the P2 M Ground Theory Heights  Heights Inter Loc Ring Frac is Multi Homog zero f2b8a8af1518 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PLocRingFrac.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_zero_f2b8a8af1518 (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«LocRingFrac».«isMultiHomog_zero» := P2M_GroundTheory_Heights__Heights_Inter_LocRingFrac_isMultiHomog_zero_f2b8a8af1518
