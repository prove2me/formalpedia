-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04
-- name    : P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:42:07.327973+00:00
-- url     : https://prove2.me/theorems/c5c8a039-ff7f-4ec3-9cf5-b9524f8a76c5
-- title:
--   P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map adjoin 2b59eaf5fe04: P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map adjoin 2b59eaf5fe04
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map adjoin 2b59eaf5fe04 construction uses the P2 M Ground Theory Heights  Heights Inter Ratio Field is Algebraic map adjoin 2b59eaf5fe04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/IsAlgebraicMapAdjoin.lean#L41-L49

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

theorem P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04 [CharZero Ω] [CharZero Φ] {d : ℕ} {t : Fin d → Ω}
    (ht : AlgebraicIndependent ℚ t) {S : Set Ω}
    (hS : ∀ w ∈ S, IsAlgebraic (IntermediateField.adjoin ℚ (Set.range t)) w) {s : Set Φ}
    (hs : ∀ n, algebraMap Ω Φ (t n) ∈ s) {z : Ω} (hz : z ∈ IntermediateField.adjoin ℚ S) :
    IsAlgebraic (IntermediateField.adjoin ℚ s) (algebraMap Ω Φ z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«RatioField».«isAlgebraic_map_adjoin» := P2M_GroundTheory_Heights__Heights_Inter_RatioField_isAlgebraic_map_adjoin_2b59eaf5fe04
