-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_disjoint_clean_parts_singleton_bad_parts
-- name    : SoficGroups.KunResidualExpanderDecomposition.disjoint_clean_parts_singleton_bad_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/582a7f7a-c75b-4bba-8147-1f90c26b6112
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.disjoint_clean_parts_singleton_bad_parts
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualExpanderDecomposition
open Filter Topology
open scoped BigOperators symmDiff

theorem SoficGroups.KunResidualExpanderDecomposition.disjoint_clean_parts_singleton_bad_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    (B : Finset V) (P : Finpartition (Finset.univ \ B)) :
    Disjoint P.parts (⊥ : Finpartition B).parts := by sorry
