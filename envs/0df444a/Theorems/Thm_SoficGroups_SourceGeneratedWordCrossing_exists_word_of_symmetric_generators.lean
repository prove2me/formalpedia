-- Prove2me | Theorems.Thm_SoficGroups_SourceGeneratedWordCrossing_exists_word_of_symmetric_generators
-- name    : SoficGroups.SourceGeneratedWordCrossing.exists_word_of_symmetric_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/ed2bbeb1-f693-4e23-8a6f-62d286275ba4
-- title:
--   SoficGroups.SourceGeneratedWordCrossing.exists_word_of_symmetric_generators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceGeneratedWordCrossing
open Filter Topology
open scoped BigOperators

theorem SoficGroups.SourceGeneratedWordCrossing.exists_word_of_symmetric_generators
    {H : Type*} [Group H]
    (S : Finset H)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set H) = ⊤)
    (g : H) :
    ∃ l : List ↥S,
      ((l.map fun i : ↥S => (i : H)).prod) = g := by sorry
