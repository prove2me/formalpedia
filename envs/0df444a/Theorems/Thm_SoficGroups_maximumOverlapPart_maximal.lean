-- Prove2me | Theorems.Thm_SoficGroups_maximumOverlapPart_maximal
-- name    : SoficGroups.maximumOverlapPart_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.999052+00:00
-- url     : https://prove2.me/theorems/3f2e59b5-8fd0-4e80-bc5a-ee2dd844faad
-- title:
--   SoficGroups.maximumOverlapPart_maximal
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

theorem SoficGroups.maximumOverlapPart_maximal
    {V : Type u} [DecidableEq V] {U : Finset V}
    (Q : Finpartition U) (C : Finset V)
    (hC : C.Nonempty) (hCU : C ⊆ U) :
    ∀ E ∈ Q.parts,
      (C ∩ E).card ≤ (C ∩ maximumOverlapPart Q C).card := by sorry
