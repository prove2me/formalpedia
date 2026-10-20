-- Prove2me | Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_conjugate_of_prefixWordAction
-- name    : SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_conjugate_of_prefixWordAction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/0ee372c0-44ab-4ccf-9695-8bedb56c7dfa
-- title:
--   SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_conjugate_of_prefixWordAction
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
universe u₁ u₂ u₃
open SoficGroups.ThompsonPrefixInsertion
open scoped commutatorElement

theorem SoficGroups.ThompsonPrefixInsertion.prefixInsertionHom_conjugate_of_prefixWordAction
    (g : BinaryLeavittˣ) (a b : List (Fin 2))
    (h : PrefixWordAction g a b) (u : BinaryLeavittˣ) :
    g * prefixInsertionHom a u * g⁻¹ = prefixInsertionHom b u := by sorry
