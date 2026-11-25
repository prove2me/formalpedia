-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chart_eval_1bd45c2a4563
-- name    : P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chart_eval_1bd45c2a4563
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:25:39.782866+00:00
-- url     : https://prove2.me/theorems/20ae164b-acaf-4f69-b9f3-506c717b039b
-- title:
--   P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart eval 1bd45c2a4563: P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart eval 1bd45c2a4563
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart eval 1bd45c2a4563 construction uses the P2 M Ground Theory Heights  Heights Inter regularity Embedding holds chart eval 1bd45c2a4563 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L129-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotMemOfNonZeroDivisor.lean#L129-L133

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExistsFunFieldMulEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotMemOfNonZeroDivisor
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
open GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chart_eval_1bd45c2a4563 {P : Ideal (MRing ι)} (τ : funField P →+* ℂ) (r : (Σ k, ι k) → funField P)
    (f : MRing ι) : τ (chartHom r f) = eval (fun p => τ (r p)) (map (Int.castRingHom ℂ) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«regularityEmbedding_holds».«chart_eval» := P2M_GroundTheory_Heights__Heights_Inter_regularityEmbedding_holds_chart_eval_1bd45c2a4563
