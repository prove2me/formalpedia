-- Prove2me | Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_mul
-- name    : SoficGroups.ThompsonPrefixInsertion.prefixWordAction_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/2e619566-dc0e-487a-8364-4bd228cc5460
-- title:
--   SoficGroups.ThompsonPrefixInsertion.prefixWordAction_mul
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

theorem SoficGroups.ThompsonPrefixInsertion.prefixWordAction_mul
    {g h : BinaryLeavittˣ} {a b c : List (Fin 2)}
    (hg : PrefixWordAction g b c)
    (hh : PrefixWordAction h a b) :
    PrefixWordAction (g * h) a c := by sorry
