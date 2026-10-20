-- Prove2me | Theorems.Thm_SoficGroups_exists_permutation_embedding_of_expanding_centralizer
-- name    : SoficGroups.exists_permutation_embedding_of_expanding_centralizer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:21.023082+00:00
-- url     : https://prove2.me/theorems/d976aa1a-40ad-4d4f-90af-43b35a1d674d
-- title:
--   SoficGroups.exists_permutation_embedding_of_expanding_centralizer
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

theorem SoficGroups.exists_permutation_embedding_of_expanding_centralizer
    {G : Type*} [Group G] (F : Finset G)
    (M : ExpandingCentralizerFiniteModel G F) :
    ∃ (n : ℕ) (f : G → Equiv.Perm (Fin n)),
      Set.InjOn f (F : Set G) ∧ f 1 = 1 ∧
        ∀ x ∈ F, ∀ y ∈ F, f (x * y) = f x * f y := by sorry
