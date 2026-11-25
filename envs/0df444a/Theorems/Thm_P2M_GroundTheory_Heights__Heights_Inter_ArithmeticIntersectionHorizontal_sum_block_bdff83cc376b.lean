-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_sum_block_bdff83cc376b
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_sum_block_bdff83cc376b
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:40:52.935201+00:00
-- url     : https://prove2.me/theorems/bca99ac7-1742-41ce-b809-a2183648d95e
-- title:
--   P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal sum block bdff83cc376b: P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal sum block bdff83cc376b
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal sum block bdff83cc376b construction uses the P2 M Ground Theory Heights  Heights Inter Arithmetic Intersection Horizontal sum block bdff83cc376b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsHorizontalImageZ.lean#L76-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalSpanXb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsHorizontalImageZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_sum_block_bdff83cc376b (F : (Σ k', ι' k') → ℕ) (k' : K') :
    ∑ i, F ⟨k', i⟩ = ∑ q, if q.1 = k' then F q else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ArithmeticIntersectionHorizontal».«sum_block» := P2M_GroundTheory_Heights__Heights_Inter_ArithmeticIntersectionHorizontal_sum_block_bdff83cc376b
