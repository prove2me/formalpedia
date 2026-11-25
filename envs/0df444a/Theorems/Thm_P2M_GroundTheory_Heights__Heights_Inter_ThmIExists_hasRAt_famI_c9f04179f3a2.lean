-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:29.841817+00:00
-- url     : https://prove2.me/theorems/adf33c1d-5862-4322-a2d7-882c3c2f9e0b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists has RAt fam I c9f04179f3a2: P2 M Ground Theory Heights  Heights Inter Thm IExists has RAt fam I c9f04179f3a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists has RAt fam I c9f04179f3a2 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists has RAt fam I c9f04179f3a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L179-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L179-L186

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
variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2 : HasRAt (famI (ι := ι)) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«hasRAt_famI» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_hasRAt_famI_c9f04179f3a2
