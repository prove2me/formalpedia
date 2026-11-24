-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:57.760338+00:00
-- url     : https://prove2.me/theorems/9f0f6f99-0fe9-42ed-83ca-9317d0a470f9
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists smooth tensor f6b0ee1175f1: P2 M Ground Theory Heights  Heights Inter Thm IExists smooth tensor f6b0ee1175f1
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists smooth tensor f6b0ee1175f1 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists smooth tensor f6b0ee1175f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L31-L33

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1 {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«smooth_tensor» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_smooth_tensor_f6b0ee1175f1
