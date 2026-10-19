-- Prove2me | Theorems.Thm_SoficGroups_SourceTopLevelCompression_sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
-- name    : SoficGroups.SourceTopLevelCompression.sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:32.70599+00:00
-- url     : https://prove2.me/theorems/d4567f72-211b-4052-803f-5fd5fb0adc91
-- title:
--   SoficGroups.SourceTopLevelCompression.sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | NonSoficGroup | external Lean 4.33.1 validation; bundle SHA256 e4e7c115f408742b878c14f4769b505077b1d17e709feeb80a84df8bd512b1c7

import Mathlib
import Definitions.Def_NonSoficGroup
set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceTopLevelCompression
open Filter

theorem SoficGroups.SourceTopLevelCompression.sourceLocalPrefixTranspositionGroup_lef_of_source_finite_models
    (hmodels :
      ∀ A : SoficGroups.SoficApproximation
          (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode),
        Tendsto (fun n => (A.model n).size) atTop atTop →
          ∀ F : Finset
              (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  SoficGroups.ThompsonPrefixLocal.sourceLocalWord),
            Nonempty (SoficGroups.ExpandingCentralizerFiniteModel
              (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
                  SoficGroups.ThompsonPrefixLocal.sourceLocalWord) F))
    (hsource : SoficGroups.Sofic
      (SoficGroups.prefixElementaryGroup SoficGroups.ninePrefixCode)) :
    SoficGroups.LEF
      (SoficGroups.ThompsonPrefixInsertion.localPrefixTranspositionGroup
        SoficGroups.ThompsonPrefixLocal.sourceLocalWord) := by sorry
