-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DualFrameSpan_sum_comp__71b2899da374
-- name    : P2M_GlobalTheory_DualFrameSpan_sum_comp__71b2899da374
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:28.814813+00:00
-- url     : https://prove2.me/theorems/9abb37ff-dc3d-4181-8cf5-db38b4d39cb4
-- title:
--   P2 M Global Theory Dual Frame Span sum comp  71b2899da374: P2 M Global Theory Dual Frame Span sum comp  71b2899da374
-- statement:
--   The P2 M Global Theory Dual Frame Span sum comp  71b2899da374 construction uses the P2 M Global Theory Dual Frame Span sum comp  71b2899da374 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L9-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualFrameSpanUnitaryRepresentation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory GlobalTheory.DualFrameSpan
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

theorem P2M_GlobalTheory_DualFrameSpan_sum_comp__71b2899da374 {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    (∑ i ∈ s, f i) ∘ₗ g = ∑ i ∈ s, f i ∘ₗ g := by sorry

alias «GlobalTheory».«DualFrameSpan».«sum_comp'» := P2M_GlobalTheory_DualFrameSpan_sum_comp__71b2899da374
