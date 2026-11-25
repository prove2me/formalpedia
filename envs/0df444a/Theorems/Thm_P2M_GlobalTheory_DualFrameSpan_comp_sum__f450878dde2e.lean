-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DualFrameSpan_comp_sum__f450878dde2e
-- name    : P2M_GlobalTheory_DualFrameSpan_comp_sum__f450878dde2e
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:05:39.415524+00:00
-- url     : https://prove2.me/theorems/875592f8-b4f9-4225-ab91-f9bc56ed0130
-- title:
--   P2 M Global Theory Dual Frame Span comp sum  f450878dde2e: P2 M Global Theory Dual Frame Span comp sum  f450878dde2e
-- statement:
--   The P2 M Global Theory Dual Frame Span comp sum  f450878dde2e construction uses the P2 M Global Theory Dual Frame Span comp sum  f450878dde2e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsDualFrameSpanUnitaryRepresentation.lean#L13-L15

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

theorem P2M_GlobalTheory_DualFrameSpan_comp_sum__f450878dde2e {ι : Type} (s : Finset ι) (f : ι → (H →ₗ[ℂ] H)) (g : H →ₗ[ℂ] H) :
    g ∘ₗ (∑ i ∈ s, f i) = ∑ i ∈ s, g ∘ₗ f i := by sorry

alias «GlobalTheory».«DualFrameSpan».«comp_sum'» := P2M_GlobalTheory_DualFrameSpan_comp_sum__f450878dde2e
