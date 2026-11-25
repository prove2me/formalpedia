-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:32.181307+00:00
-- url     : https://prove2.me/theorems/e1ab3a73-7e99-42b1-969e-a2c753c6d425
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms sum fin staircase 57c59d30c9c9: P2 M Ground Theory Heights  Heights Rest Terms sum fin staircase 57c59d30c9c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms sum fin staircase 57c59d30c9c9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms sum fin staircase 57c59d30c9c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchNonHookResidues.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchNonHookResidues.lean#L10-L12

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchNonHookResidues
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9 (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«sum_fin_staircase» := P2M_GroundTheory_Heights__Heights_RestTerms_sum_fin_staircase_57c59d30c9c9
