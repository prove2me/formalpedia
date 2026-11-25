-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:44:43.116683+00:00
-- url     : https://prove2.me/theorems/cc1ac357-ee67-412b-b1ca-fe8de4f6133c
-- title:
--   P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map f9ef88b8fca0: P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map f9ef88b8fca0
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map f9ef88b8fca0 construction uses the P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map f9ef88b8fca0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L22-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StWWRatioBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsAlgebraicMapAdjoin
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
open ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
variable {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0 [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {z : Ω} (hz : IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) z)
    {s : Set Φ} (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RatioField».«isAlgebraic_map» := P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_f9ef88b8fca0
