-- Prove2me | Theorems.Thm_SoficGroups_SourceProductThroughAlpha_sourceCompressedLocalProductEmbedding_factors_through_alpha
-- name    : SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductEmbedding_factors_through_alpha
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/f5be5162-6ae4-4091-b847-bda92f078ea6
-- title:
--   SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductEmbedding_factors_through_alpha
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

theorem SoficGroups.SourceProductThroughAlpha.sourceCompressedLocalProductEmbedding_factors_through_alpha :
    SoficGroups.SourceGeneratedWordCrossing.sourceAlphaInclusion.comp
        sourceCompressedLocalProductToAlpha =
      SoficGroups.ThompsonPrefixInsertion.sourceCompressedLocalProductEmbedding := by sorry
