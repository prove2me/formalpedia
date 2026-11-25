-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:40.342187+00:00
-- url     : https://prove2.me/theorems/3079aad0-bc96-4131-a11b-5049c31aeddf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom injective b1bcc0d5fe5b: P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom injective b1bcc0d5fe5b
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom injective b1bcc0d5fe5b construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom injective b1bcc0d5fe5b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L95-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L95-L113

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b (N : ℕ) : Function.Injective (powerSumHom N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«powerSumHom_injective» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_injective_b1bcc0d5fe5b
