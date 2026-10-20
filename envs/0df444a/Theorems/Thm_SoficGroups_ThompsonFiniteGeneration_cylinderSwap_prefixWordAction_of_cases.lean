-- Prove2me | Theorems.Thm_SoficGroups_ThompsonFiniteGeneration_cylinderSwap_prefixWordAction_of_cases
-- name    : SoficGroups.ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.748479+00:00
-- url     : https://prove2.me/theorems/7a452b62-a160-402e-ba45-e3191e03999d
-- title:
--   SoficGroups.ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
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
open SoficGroups.ThompsonFiniteGeneration
open ThompsonPrefixInsertion

theorem SoficGroups.ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
    {a b w v : List (Fin 2)}
    (hab : ¬ a <+: b) (hba : ¬ b <+: a)
    (hcase :
      (a <+: w ∧ v = b ++ w.drop a.length) ∨
      (b <+: w ∧ v = a ++ w.drop b.length) ∨
      (v = w ∧ ¬ a <+: w ∧ ¬ w <+: a ∧
        ¬ b <+: w ∧ ¬ w <+: b)) :
    PrefixWordAction (cylinderSwap a b hab hba) w v := by sorry
