-- Prove2me | Theorems.Thm_SoficGroups_SourceProductThroughAlpha_boundary_sourceCompressedGeneratorSubtypeEquiv
-- name    : SoficGroups.SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:33.785013+00:00
-- url     : https://prove2.me/theorems/b923e05a-1676-44ab-a5e7-bf81869f5141
-- title:
--   SoficGroups.SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open scoped BigOperators

theorem SoficGroups.SourceProductThroughAlpha.boundary_sourceCompressedGeneratorSubtypeEquiv
    {V : Type*} [DecidableEq V]
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (σ : ↥(sourceCompressedGeneratingFinset SΓ) → Equiv.Perm V)
    (E : Finset V) :
    SoficGroups.boundary
      (fun i : ↥SΓ =>
        σ (sourceCompressedGeneratorSubtypeEquiv SΓ i)) E =
      SoficGroups.boundary σ E := by sorry
