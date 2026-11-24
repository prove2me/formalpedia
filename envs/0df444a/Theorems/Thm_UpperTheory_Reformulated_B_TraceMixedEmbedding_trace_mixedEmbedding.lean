-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_TraceMixedEmbedding_trace_mixedEmbedding
-- name    : UpperTheory.Reformulated.B.TraceMixedEmbedding.trace_mixedEmbedding
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:43:40.976831+00:00
-- url     : https://prove2.me/theorems/58686330-f2f4-4983-b4ca-c6fe6d1e7b89
-- title:
--   Trace Mixed Embedding: trace mixed Embedding
-- statement:
--   The Trace Mixed Embedding construction uses the trace mixed Embedding property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TraceMixedEmbedding.lean#L3-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/TraceMixedEmbedding.lean#L3-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TraceMixedEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.TraceMixedEmbedding.trace_mixedEmbedding :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
    (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
        ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
      (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by sorry
