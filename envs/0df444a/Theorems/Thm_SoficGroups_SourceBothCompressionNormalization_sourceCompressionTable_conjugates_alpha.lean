-- Prove2me | Theorems.Thm_SoficGroups_SourceBothCompressionNormalization_sourceCompressionTable_conjugates_alpha
-- name    : SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:29.358829+00:00
-- url     : https://prove2.me/theorems/80d6d833-52e0-4c14-881d-38c7542c0374
-- title:
--   SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceBothCompressionNormalization

theorem SoficGroups.SourceBothCompressionNormalization.sourceCompressionTable_conjugates_alpha
    (i : Fin 2)
    (g : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode) :
    ∃ k : SoficGroups.prefixElementaryGroup SoficGroups.alphaPrefixCode,
      sourceCompressionTable i * sourceAlphaElement g *
          (sourceCompressionTable i)⁻¹ =
        sourceAlphaElement k := by sorry
