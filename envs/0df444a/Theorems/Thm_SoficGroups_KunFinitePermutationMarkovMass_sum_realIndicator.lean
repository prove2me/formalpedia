-- Prove2me | Theorems.Thm_SoficGroups_KunFinitePermutationMarkovMass_sum_realIndicator
-- name    : SoficGroups.KunFinitePermutationMarkovMass.sum_realIndicator
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:26.206993+00:00
-- url     : https://prove2.me/theorems/8c604f2f-5bf6-4c4b-9880-2657e2a6cf69
-- title:
--   SoficGroups.KunFinitePermutationMarkovMass.sum_realIndicator
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunFinitePermutationMarkovMass
open scoped BigOperators

theorem SoficGroups.KunFinitePermutationMarkovMass.sum_realIndicator {V : Type*}
    [Fintype V] [DecidableEq V] (T : Finset V) :
    (∑ x : V, realIndicator T x) = (T.card : ℝ) := by sorry
