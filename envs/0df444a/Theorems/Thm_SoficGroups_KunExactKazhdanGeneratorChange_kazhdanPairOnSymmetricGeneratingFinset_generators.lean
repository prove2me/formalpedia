-- Prove2me | Theorems.Thm_SoficGroups_KunExactKazhdanGeneratorChange_kazhdanPairOnSymmetricGeneratingFinset_generators
-- name    : SoficGroups.KunExactKazhdanGeneratorChange.kazhdanPairOnSymmetricGeneratingFinset_generators
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:30.418361+00:00
-- url     : https://prove2.me/theorems/c922b3f8-6b71-47f8-9ba3-05b9f3571036
-- title:
--   SoficGroups.KunExactKazhdanGeneratorChange.kazhdanPairOnSymmetricGeneratingFinset_generators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunExactKazhdanGeneratorChange
universe u v

theorem SoficGroups.KunExactKazhdanGeneratorChange.kazhdanPairOnSymmetricGeneratingFinset_generators
    {G : Type u} [Group G]
    (P : SoficGroups.KazhdanPair.{u, v} G)
    (S : Finset G)
    (hsymmetric : ∀ g ∈ S, g⁻¹ ∈ S)
    (hgenerates : Subgroup.closure (S : Set G) = ⊤) :
    (kazhdanPairOnSymmetricGeneratingFinset
      P S hsymmetric hgenerates).generators = S := by sorry
