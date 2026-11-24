-- Prove2me | Theorems.Thm_ValueAwareRR_reversedRepresentativeFirst_ge_two
-- name    : ValueAwareRR.reversedRepresentativeFirst_ge_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:58:46.217082+00:00
-- url     : https://prove2.me/theorems/7fc9a375-b063-40a3-af59-e5001374fb3b
-- title:
--   Value Aware RR: reversed Representative First ge two
-- statement:
--   The Value Aware RR construction uses the reversed Representative First ge two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L74-L76
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L74-L76

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.reversedRepresentativeFirst_ge_two (r : Representative) :
    2 ≤ (negateLabel (representativeOrder r 0)).val := by sorry
