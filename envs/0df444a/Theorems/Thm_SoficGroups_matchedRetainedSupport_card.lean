-- Prove2me | Theorems.Thm_SoficGroups_matchedRetainedSupport_card
-- name    : SoficGroups.matchedRetainedSupport_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:19.258421+00:00
-- url     : https://prove2.me/theorems/469de31b-5baa-415e-98cb-7ab78f53fd06
-- title:
--   SoficGroups.matchedRetainedSupport_card
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

theorem SoficGroups.matchedRetainedSupport_card
    {V : Type*} [DecidableEq V] {U : Finset V}
    (P : Finpartition U) (R : Finset (Finset V))
    (hR : R ⊆ P.parts) :
    (matchedRetainedSupport R).card = ∑ C ∈ R, C.card := by sorry
