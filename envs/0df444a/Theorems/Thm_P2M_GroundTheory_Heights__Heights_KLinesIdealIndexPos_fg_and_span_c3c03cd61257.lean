-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257
-- name    : P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:02.700297+00:00
-- url     : https://prove2.me/theorems/c1f268b1-39de-44ba-b09f-e2bcb14e0def
-- title:
--   P2 M Ground Theory Heights  Heights KLines Ideal Index Pos fg and span c3c03cd61257: P2 M Ground Theory Heights  Heights KLines Ideal Index Pos fg and span c3c03cd61257
-- statement:
--   The P2 M Ground Theory Heights  Heights KLines Ideal Index Pos fg and span c3c03cd61257 construction uses the P2 M Ground Theory Heights  Heights KLines Ideal Index Pos fg and span c3c03cd61257 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealIndexPos.lean#L21-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PLinesIdealIndexPos.lean#L21-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PLinesIdealIndexPos
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField
open scoped nonZeroDivisors
open GroundTheory.Heights₂.Heights.KLinesIdealIndexPos
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257 (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) :
    (((J : Submodule (𝓞 K) K).map (toOne K)).restrictScalars ℤ).FG ∧
      Submodule.span K (((J : Submodule (𝓞 K) K).map (toOne K) : Submodule (𝓞 K) (Unit → K)) :
        Set (Unit → K)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«KLinesIdealIndexPos».«fg_and_span» := P2M_GroundTheory_Heights__Heights_KLinesIdealIndexPos_fg_and_span_c3c03cd61257
