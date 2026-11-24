-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:13.917028+00:00
-- url     : https://prove2.me/theorems/7b9ba883-ff2e-41c5-b981-186db811f20b
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection wh prod X pow 7859ccdd4b43: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection wh prod X pow 7859ccdd4b43
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection wh prod X pow 7859ccdd4b43 construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection wh prod X pow 7859ccdd4b43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L53-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsFieldIntersectionNoBlockFam
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogRenameCoordPow
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
open GroundTheory.Heights₂.Heights.Inter.PushforwardArithIntersection
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43 {K₀ : Type} [Fintype K₀] (q : K₀ → Σ k, ι k) (α : K₀ → ℕ) :
    IsWeightedHomogeneous (blkW (ι := ι)) (∏ k, (X (q k) : MRing ι) ^ α k) (∑ k, α k • blkW (q k)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«wh_prod_X_pow» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_wh_prod_X_pow_7859ccdd4b43
