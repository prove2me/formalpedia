-- Prove2me | Theorems.Thm_SoficGroups_KunResidualExpanderDecomposition_close_residual_inter_properties
-- name    : SoficGroups.KunResidualExpanderDecomposition.close_residual_inter_properties
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:27.241177+00:00
-- url     : https://prove2.me/theorems/a6fd1c07-887f-4fff-9ed1-66ab2fb8c1aa
-- title:
--   SoficGroups.KunResidualExpanderDecomposition.close_residual_inter_properties
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

theorem SoficGroups.KunResidualExpanderDecomposition.close_residual_inter_properties {V : Type*} [DecidableEq V]
    (R T U : Finset V) (hTR : T ⊆ R)
    (hclose : 3 * (U ∆ T).card < T.card) :
    (R ∩ U).Nonempty ∧
      U.card ≤ 2 * (R ∩ U).card ∧
      (R ∩ U).card < 2 * T.card := by sorry
