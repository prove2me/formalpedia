-- Prove2me | Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_injective
-- name    : SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/a8ee373a-0a2a-4583-9865-354705dbb2d0
-- title:
--   SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_injective
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ThompsonPrefixInsertion
open scoped BigOperators

theorem SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_injective (a : List (Fin 2)) :
    Function.Injective (prefixInsertionHom a) := by sorry
