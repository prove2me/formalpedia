-- Prove2me | Theorems.Thm_SoficGroups_finpartition_dominant_matching_injOn
-- name    : SoficGroups.finpartition_dominant_matching_injOn
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/00241eb8-3a55-4c00-ac19-a6f6c4e73648
-- title:
--   SoficGroups.finpartition_dominant_matching_injOn
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

theorem SoficGroups.finpartition_dominant_matching_injOn
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) (D : Finset V → Finset V)
    (hmajor : ∀ C ∈ R, (D C).card < 2 * (C ∩ D C).card) :
    Set.InjOn D (R : Set (Finset V)) := by sorry
