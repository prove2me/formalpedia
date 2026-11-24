-- Prove2me | Theorems.Thm_ValueAwareRR_fourPermutation_card
-- name    : ValueAwareRR.fourPermutation_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:59:22.575889+00:00
-- url     : https://prove2.me/theorems/d240a8fb-c9b0-41e6-9270-8ae855b71dac
-- title:
--   Value Aware RR: four Permutation card
-- statement:
--   There are exactly twenty-four permutations of four labels.
--
--   Source: https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L113-L114
-- source:
--   https://github.com/ipitchford/random-reshuffling-baseline-policy/blob/f25d574a8febb0fe2120e592101983e2a0d97c93/ValueAwareRR/ProxyCounterexample.lean#L113-L114

import Mathlib
import Definitions.Def_ValueAwareRR_ProxyCounterexample
set_option autoImplicit true
open ValueAwareRR

theorem ValueAwareRR.fourPermutation_card : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by sorry
