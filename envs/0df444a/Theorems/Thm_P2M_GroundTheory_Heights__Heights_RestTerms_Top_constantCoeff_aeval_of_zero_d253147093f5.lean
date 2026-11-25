-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:21:12.282894+00:00
-- url     : https://prove2.me/theorems/8f4ea546-3a19-5672-9b41-eb2ab46a8865
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff aeval of zero d253147093f5: P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff aeval of zero d253147093f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff aeval of zero d253147093f5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top constant Coeff aeval of zero d253147093f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L221-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L221-L228

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5 {ι κ : Type*} (g : ι → MvPolynomial κ ℚ)
    (hg : ∀ i, constantCoeff (g i) = 0) (p : MvPolynomial ι ℚ) :
    constantCoeff (aeval g p) = constantCoeff p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«constantCoeff_aeval_of_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_constantCoeff_aeval_of_zero_d253147093f5
