-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e
-- name    : P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:44:07.903401+00:00
-- url     : https://prove2.me/theorems/214f623e-409b-4282-b857-428ff60c967d
-- title:
--   P2 M Ground Theory Heights  Heights nonempty height One Spectrum 8a32eca7b64e: P2 M Ground Theory Heights  Heights nonempty height One Spectrum 8a32eca7b64e
-- statement:
--   The P2 M Ground Theory Heights  Heights nonempty height One Spectrum 8a32eca7b64e construction uses the P2 M Ground Theory Heights  Heights nonempty height One Spectrum 8a32eca7b64e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L187-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L187-L190

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsLocal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_StatementsExamples
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
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e : Nonempty (HeightOneSpectrum (𝓞 K)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«nonempty_heightOneSpectrum» := P2M_GroundTheory_Heights__Heights_nonempty_heightOneSpectrum_8a32eca7b64e
