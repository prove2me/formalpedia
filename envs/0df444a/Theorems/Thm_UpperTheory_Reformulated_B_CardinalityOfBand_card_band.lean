-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_CardinalityOfBand_card_band
-- name    : UpperTheory.Reformulated.B.CardinalityOfBand.card_band
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:09.769868+00:00
-- url     : https://prove2.me/theorems/208e6c85-7374-4a4a-91a3-9de69fc91b00
-- title:
--   Cardinality Of Band: card band
-- statement:
--   The Cardinality Of Band construction uses the card band property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardinalityOfBand.lean#L10-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CardinalityOfBand.lean#L10-L25

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CardinalityOfBand
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.CardinalityOfBand.card_band :
    ∀ (m a b : Nat),
      @LE.le Nat instLENat b m →
        @Eq Nat (@Finset.card (Fin m) {i : Fin m | @Eq Bool (UpperTheory.Reformulated.B.CardinalityOfBand.band m a b i) Bool.true})
          (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) b a) := by sorry
