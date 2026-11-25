-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_P6_r20a_finsum_const_eq_card_mul
-- name    : UpperTheory.Reformulated.B.P6.r20a.finsum_const_eq_card_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:12:41.820794+00:00
-- url     : https://prove2.me/theorems/534afdd5-bc08-4d8c-954b-75f64ee35c66
-- title:
--   r20a: finsum const eq card mul
-- statement:
--   The r20a construction uses the finsum const eq card mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SchwartzBilinear/QuotientOutRightInvariant.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_QuotientOutRightInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r20a

theorem UpperTheory.Reformulated.B.P6.r20a.finsum_const_eq_card_mul {α : Type} [Finite α] (c : ℂ) : ∑ᶠ _ : α, c = (Nat.card α : ℂ) * c := by sorry
