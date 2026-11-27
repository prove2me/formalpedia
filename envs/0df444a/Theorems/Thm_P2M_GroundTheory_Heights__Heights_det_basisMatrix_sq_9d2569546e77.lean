-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_det_basisMatrix_sq_9d2569546e77
-- name    : P2M_GroundTheory_Heights__Heights_det_basisMatrix_sq_9d2569546e77
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:46.169948+00:00
-- url     : https://prove2.me/theorems/5033aa16-e499-5b2f-a7cb-e346a14c4567
-- title:
--   P2 M Ground Theory Heights  Heights det basis Matrix sq 9d2569546e77: P2 M Ground Theory Heights  Heights det basis Matrix sq 9d2569546e77
-- statement:
--   The P2 M Ground Theory Heights  Heights det basis Matrix sq 9d2569546e77 construction uses the P2 M Ground Theory Heights  Heights det basis Matrix sq 9d2569546e77 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Covolume.lean#L35-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Covolume.lean#L35-L41

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HermitianEuclidean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeExact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Covolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix MeasureTheory Module
open scoped Kronecker
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open Classical

theorem P2M_GroundTheory_Heights__Heights_det_basisMatrix_sq_9d2569546e77 : (basisMatrix K).det ^ 2 = ((discr K : ℤ) : ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«det_basisMatrix_sq» := P2M_GroundTheory_Heights__Heights_det_basisMatrix_sq_9d2569546e77
