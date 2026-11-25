-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:18:54.486434+00:00
-- url     : https://prove2.me/theorems/550f37b7-bcbf-4c8f-8e05-7a39848990e1
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv smul b0bc8a006225: P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv smul b0bc8a006225
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv smul b0bc8a006225 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Conj Int Num quot Equiv smul b0bc8a006225 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L56-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PConjIntNum.lean#L56-L64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsConjIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PConjIntNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial NumbersDVR
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.ConjIntNum
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type} [Field F]
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225 (τ : F ≃+* F) (J : Ideal (MRing ι F)) (c : F) (x : MRing ι F ⧸ J) :
    quotEquiv τ J (c • x) = τ c • quotEquiv τ J x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ConjIntNum».«quotEquiv_smul» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ConjIntNum_quotEquiv_smul_b0bc8a006225
