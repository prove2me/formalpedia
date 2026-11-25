-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064
-- name    : P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:46:50.55023+00:00
-- url     : https://prove2.me/theorems/a1b90eb7-7a87-4a93-8c4f-13afeed9830d
-- title:
--   P2 M Ground Theory Heights  Heights height add ring Krull Dim quotient le 42493816d064: P2 M Ground Theory Heights  Heights height add ring Krull Dim quotient le 42493816d064
-- statement:
--   The P2 M Ground Theory Heights  Heights height add ring Krull Dim quotient le 42493816d064 construction uses the P2 M Ground Theory Heights  Heights height add ring Krull Dim quotient le 42493816d064 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/HeightCoheightQuotient.lean#L15-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HeightCoheightQuotient
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

theorem P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064 {B : Type*} [CommRing B] (P : Ideal B) [hP : P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (B ⧸ P) ≤ ringKrullDim B := by sorry

alias «GroundTheory».«Heights₂».«Heights».«height_add_ringKrullDim_quotient_le» := P2M_GroundTheory_Heights__Heights_height_add_ringKrullDim_quotient_le_42493816d064
