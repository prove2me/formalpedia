-- Prove2me | Theorems.Thm_ValueAwareRR_encodedPermutation_surjective
-- name    : ValueAwareRR.encodedPermutation_surjective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T09:06:12.575646+00:00
-- url     : https://prove2.me/theorems/508a92db-863c-4a11-8576-9f234566672a
-- title:
--   Value Aware RR: encoded Permutation surjective
-- statement:
--   The Value Aware RR construction uses the encoded Permutation surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L127-L128
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L127-L128

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.encodedPermutation_surjective : Function.Surjective encodedPermutation := by sorry
