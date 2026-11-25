-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:56:52.059303+00:00
-- url     : https://prove2.me/theorems/1ce8a9d6-d7e0-5709-aa41-3a1fb3076b08
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant comp perm 6bc028974320: P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant comp perm 6bc0289743
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant comp perm 6bc028974320 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Sch Concat Alternant alternant comp perm 6bc028974320 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchConcatAlternant.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchConcatAlternant.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchConcatAlternant
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320 {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«SchConcatAlternant».«alternant_comp_perm» := P2M_GroundTheory_Heights__Heights_RestTerms_SchConcatAlternant_alternant_comp_perm_6bc028974320
