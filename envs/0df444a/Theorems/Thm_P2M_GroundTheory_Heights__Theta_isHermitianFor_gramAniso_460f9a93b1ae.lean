-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isHermitianFor_gramAniso_460f9a93b1ae
-- name    : P2M_GroundTheory_Heights__Theta_isHermitianFor_gramAniso_460f9a93b1ae
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:13.423639+00:00
-- url     : https://prove2.me/theorems/6470e03a-80b0-5e85-833f-573579892b15
-- title:
--   P2 M Ground Theory Heights  Theta is Hermitian For gram Aniso 460f9a93b1ae: P2 M Ground Theory Heights  Theta is Hermitian For gram Aniso 460f9a93b1ae
-- statement:
--   The P2 M Ground Theory Heights  Theta is Hermitian For gram Aniso 460f9a93b1ae construction uses the P2 M Ground Theory Heights  Theta is Hermitian For gram Aniso 460f9a93b1ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L74-L79

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

theorem P2M_GroundTheory_Heights__Theta_isHermitianFor_gramAniso_460f9a93b1ae : IsHermitianFor (conjHom ℚ GaussQ) gramAniso := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isHermitianFor_gramAniso» := P2M_GroundTheory_Heights__Theta_isHermitianFor_gramAniso_460f9a93b1ae
