-- Prove2me | Theorems.Thm_SoficGroups_SourceProductThroughAlpha_exists_sourceCompressedKazhdanPair_with_same_generators
-- name    : SoficGroups.SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/5475c05d-a873-45cd-ae3f-0c236f49b592
-- title:
--   SoficGroups.SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceProductThroughAlpha
open Filter Topology
open scoped BigOperators
universe v

theorem SoficGroups.SourceProductThroughAlpha.exists_sourceCompressedKazhdanPair_with_same_generators
    (SΓ : Finset
      (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode))
    (hsymmetric : ∀ g ∈ SΓ, g⁻¹ ∈ SΓ)
    (hgenerates : Subgroup.closure
      (SΓ : Set
        (SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode)) =
          ⊤) :
    ∃ P : SoficGroups.KazhdanPair.{0, v}
        (SoficGroups.prefixElementaryGroup
          SoficGroups.alphaZeroPrefixCode),
      P.generators = sourceCompressedGeneratingFinset SΓ := by sorry
