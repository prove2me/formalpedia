-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SpanTopFamily_span_top
-- name    : UpperTheory.Reformulated.B.SpanTopFamily.span_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:20.83353+00:00
-- url     : https://prove2.me/theorems/c30df721-b96b-4373-9a34-1b2a82899a22
-- title:
--   Span Top Family: span top
-- statement:
--   The Span Top Family construction uses the span top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanTopFamily.lean#L13-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SpanTopFamily.lean#L13-L47

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SpanTopFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.SpanTopFamily.span_top :
    ∀ {E K : Type} [inst : Field E] [NumberField E] [inst_2 : Field K] (O : ValuationSubring K) (ι : E →+* K) {n : Type}
      [Fintype n] [DecidableEq n] (L : Submodule (NumberField.RingOfIntegers E) (n → E)),
      Submodule.span E (↑L : Set (n → E)) = ⊤ → Submodule.span K (↑(UpperTheory.Reformulated.B.SpanTopFamily.Mι O ι L) : Set (n → K)) = ⊤ := by sorry
