-- Prove2me | Theorems.Thm_SoficGroups_exists_local_word_control
-- name    : SoficGroups.exists_local_word_control
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/7018b5da-d1b9-4f13-bb01-067badb5d288
-- title:
--   SoficGroups.exists_local_word_control
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

theorem SoficGroups.exists_local_word_control {α : Type u} {G : Type v} [Group G]
    (φ : FreeGroup α →* G) (z : FreeGroup α) :
    ∃ s : Finset G, ∀ (H : Type w) [Group H] (f : G → H),
      LocalMultiplicativeOn s f →
        FreeGroup.lift (fun a => f (φ (FreeGroup.of a))) z = f (φ z) := by sorry
