-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_wdAt_zero_e03b9480a50b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_wdAt_zero_e03b9480a50b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:24:35.750406+00:00
-- url     : https://prove2.me/theorems/afe46ae4-da75-46f7-81d0-1130b2887338
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists wd At zero e03b9480a50b: P2 M Ground Theory Heights  Heights Inter Thm IExists wd At zero e03b9480a50b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists wd At zero e03b9480a50b construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists wd At zero e03b9480a50b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L211-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L211-L215

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_wdAt_zero_e03b9480a50b (hD1 : RegularityIndependence.Statement) : WDAt (famI (ι := ι)) 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«wdAt_zero» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_wdAt_zero_e03b9480a50b
