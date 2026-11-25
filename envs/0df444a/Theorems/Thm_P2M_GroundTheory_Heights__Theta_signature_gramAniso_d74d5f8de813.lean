-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_signature_gramAniso_d74d5f8de813
-- name    : P2M_GroundTheory_Heights__Theta_signature_gramAniso_d74d5f8de813
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:26.527051+00:00
-- url     : https://prove2.me/theorems/73cbc02d-8435-40b1-84b2-621541816604
-- title:
--   P2 M Ground Theory Heights  Theta signature gram Aniso d74d5f8de813: P2 M Ground Theory Heights  Theta signature gram Aniso d74d5f8de813
-- statement:
--   The P2 M Ground Theory Heights  Theta signature gram Aniso d74d5f8de813 construction uses the P2 M Ground Theory Heights  Theta signature gram Aniso d74d5f8de813 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L88-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L88-L95

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_GaussianExample
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Automorphic Matrix

theorem P2M_GroundTheory_Heights__Theta_signature_gramAniso_d74d5f8de813 :
    gaussValue gramAniso ![1, 0] = algebraMap ℚ GaussQ 1 ∧
      gaussValue gramAniso ![0, 1] = algebraMap ℚ GaussQ (-3) ∧ (0 : ℚ) < 1 ∧ (-3 : ℚ) < 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«signature_gramAniso» := P2M_GroundTheory_Heights__Theta_signature_gramAniso_d74d5f8de813
