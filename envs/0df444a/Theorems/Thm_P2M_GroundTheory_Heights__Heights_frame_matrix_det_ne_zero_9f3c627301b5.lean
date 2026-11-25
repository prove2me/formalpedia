-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_frame_matrix_det_ne_zero_9f3c627301b5
-- name    : P2M_GroundTheory_Heights__Heights_frame_matrix_det_ne_zero_9f3c627301b5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:47:15.424198+00:00
-- url     : https://prove2.me/theorems/bbc5785d-d79f-461a-8948-da004a55827d
-- title:
--   P2 M Ground Theory Heights  Heights frame matrix det ne zero 9f3c627301b5: P2 M Ground Theory Heights  Heights frame matrix det ne zero 9f3c627301b5
-- statement:
--   The P2 M Ground Theory Heights  Heights frame matrix det ne zero 9f3c627301b5 construction uses the P2 M Ground Theory Heights  Heights frame matrix det ne zero 9f3c627301b5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameJacobianGeneric.lean#L14-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PFrameJacobianGeneric.lean#L14-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameJacobianGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StConormalGenerationGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PFrameJacobianGeneric
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
noncomputable section
open MvPolynomial
open scoped Matrix

theorem P2M_GroundTheory_Heights__Heights_frame_matrix_det_ne_zero_9f3c627301b5 {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«frame_matrix_det_ne_zero» := P2M_GroundTheory_Heights__Heights_frame_matrix_det_ne_zero_9f3c627301b5
