-- Prove2me | Theorems.Thm_ValueAwareRR_encodedPermutation_bijective
-- name    : ValueAwareRR.encodedPermutation_bijective
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T08:59:31.008706+00:00
-- url     : https://prove2.me/theorems/b3b124d8-bf39-4623-b650-b5754d4b8ea3
-- title:
--   Value Aware RR: encoded Permutation bijective
-- statement:
--   The encoding is onto the ordinary permutation type, not merely a list of examples.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L123-L125
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L123-L125

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.encodedPermutation_bijective : Function.Bijective encodedPermutation := by sorry
