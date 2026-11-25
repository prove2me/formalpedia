-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_gaussQ_im_0bf2c7b57145
-- name    : P2M_GroundTheory_Heights__Theta_conj_gaussQ_im_0bf2c7b57145
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:44.360812+00:00
-- url     : https://prove2.me/theorems/f791bf55-62c0-46b3-a746-6f5a8392fe8a
-- title:
--   P2 M Ground Theory Heights  Theta conj gauss Q im 0bf2c7b57145: P2 M Ground Theory Heights  Theta conj gauss Q im 0bf2c7b57145
-- statement:
--   The P2 M Ground Theory Heights  Theta conj gauss Q im 0bf2c7b57145 construction uses the P2 M Ground Theory Heights  Theta conj gauss Q im 0bf2c7b57145 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L49-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L49-L50

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

theorem P2M_GroundTheory_Heights__Theta_conj_gaussQ_im_0bf2c7b57145 (z : GaussQ) : (conj ℚ GaussQ z).im = -z.im := by sorry

alias «GroundTheory».«Heights₂».«Theta».«conj_gaussQ_im» := P2M_GroundTheory_Heights__Theta_conj_gaussQ_im_0bf2c7b57145
