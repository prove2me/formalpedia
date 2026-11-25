-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:06.739176+00:00
-- url     : https://prove2.me/theorems/a6cf4749-a1cf-45a6-b516-9cea7ca6ba7f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists all dims 7eb7dcfabea6: P2 M Ground Theory Heights  Heights Inter Thm IExists all dims 7eb7dcfabea6
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists all dims 7eb7dcfabea6 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists all dims 7eb7dcfabea6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L217-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L217-L226

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6 (hD1 : RegularityIndependence.Statement) (hMul : RMulStatement)
    (hstep : ∀ n, HasRAt (famI (ι := ι)) n → LastAddAt (famI (ι := ι)) n → WDAt (famI (ι := ι)) (n + 1))
    (n : ℕ) : WDAt (famI (ι := ι)) n ∧ HasRAt (famI (ι := ι)) n ∧ LastAddAt (famI (ι := ι)) n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«all_dims» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_all_dims_7eb7dcfabea6
