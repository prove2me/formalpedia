-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:40.473052+00:00
-- url     : https://prove2.me/theorems/e4ff9f07-b5d8-42ce-8ebf-49f6eb71cfbb
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements log abs Norm height One Spectrum nonneg 363f17010b7e: P2 M Ground Theory Heights  Heights Nine Statements log abs Norm height One Spectrum nonneg 36
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements log abs Norm height One Spectrum nonneg 363f17010b7e construction uses the P2 M Ground Theory Heights  Heights Nine Statements log abs Norm height One Spectrum nonneg 363f17010b7e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/PNormCountBound.lean#L34-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_PNormCountBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e {L : Type} [Field L] [NumberField L]
    (v : HeightOneSpectrum (𝓞 L)) : 0 ≤ Real.log (Ideal.absNorm v.asIdeal : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«log_absNorm_heightOneSpectrum_nonneg» := P2M_GroundTheory_Heights__Heights_NineStatements_log_absNorm_heightOneSpectrum_nonneg_363f17010b7e
