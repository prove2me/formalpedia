-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14
-- name    : P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:45:17.540436+00:00
-- url     : https://prove2.me/theorems/b6e5fda8-11ba-5f8c-86f5-1a0fceb2c11a
-- title:
--   P2 M Ground Theory Heights  Heights det gram im 04e273c56d14: P2 M Ground Theory Heights  Heights det gram im 04e273c56d14
-- statement:
--   The P2 M Ground Theory Heights  Heights det gram im 04e273c56d14 construction uses the P2 M Ground Theory Heights  Heights det gram im 04e273c56d14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L68-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithDegreeExact.lean#L68-L70

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14 {n : Type*} [Fintype n] [DecidableEq n] (v : n → V) :
    (det (gram ℂ v)).im = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_gram_im» := P2M_GroundTheory_Heights__Heights_det_gram_im_04e273c56d14
