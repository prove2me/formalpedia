-- Prove2me | Theorems.Thm_ValueAwareRR_encodedPermutation_injective
-- name    : ValueAwareRR.encodedPermutation_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:59:14.935391+00:00
-- url     : https://prove2.me/theorems/19b124c9-e4dd-4601-b74c-9a138b311236
-- title:
--   Value Aware RR: encoded Permutation injective
-- statement:
--   The Value Aware RR construction uses the encoded Permutation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L102-L106
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L102-L106

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.encodedPermutation_injective : Function.Injective encodedPermutation := by sorry
