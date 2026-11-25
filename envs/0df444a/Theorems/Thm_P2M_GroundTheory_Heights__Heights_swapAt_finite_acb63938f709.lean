-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_swapAt_finite_acb63938f709
-- name    : P2M_GroundTheory_Heights__Heights_swapAt_finite_acb63938f709
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:50:53.448524+00:00
-- url     : https://prove2.me/theorems/2e554131-f17c-507b-91d9-937ae93a99ae
-- title:
--   P2 M Ground Theory Heights  Heights swap At finite acb63938f709: P2 M Ground Theory Heights  Heights swap At finite acb63938f709
-- statement:
--   The P2 M Ground Theory Heights  Heights swap At finite acb63938f709 construction uses the P2 M Ground Theory Heights  Heights swap At finite acb63938f709 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L217-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/StatementsExamples.lean#L217-L221

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

theorem P2M_GroundTheory_Heights__Heights_swapAt_finite_acb63938f709 (v₀ : HeightOneSpectrum (𝓞 K)) : {v | swapAt v₀ v ≠ 1}.Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«swapAt_finite» := P2M_GroundTheory_Heights__Heights_swapAt_finite_acb63938f709
