-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:41:45.245785+00:00
-- url     : https://prove2.me/theorems/ae1fc75d-bdf6-4704-bf57-0166fa15ac92
-- title:
--   P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection sum single eq extend 60ee0a6ba5cd: P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection sum single eq exten
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection sum single eq extend 60ee0a6ba5cd construction uses the P2 M Ground Theory Heights  Heights Inter Pushforward Arith Intersection sum single eq extend 60ee0a6ba5cd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L35-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsMultiHomogRenameCoordPow.lean#L35-L49

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
omit [Fintype K]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd {K₀ : Type} [Fintype K₀] (κ : K₀ → K) (hκ : Function.Injective κ) (α : K₀ → ℕ) :
    (∑ k, α k • (Pi.single (κ k) 1 : K → ℕ)) = Function.extend κ α 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PushforwardArithIntersection».«sum_single_eq_extend» := P2M_GroundTheory_Heights__Heights_Inter_PushforwardArithIntersection_sum_single_eq_extend_60ee0a6ba5cd
