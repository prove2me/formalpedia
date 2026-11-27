-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_conj_gaussQ_re_b971a3ac9b26
-- name    : P2M_GroundTheory_Heights__Theta_conj_gaussQ_re_b971a3ac9b26
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:40.229414+00:00
-- url     : https://prove2.me/theorems/2c60edbe-9c12-40ae-a06f-410a4f4cf162
-- title:
--   P2 M Ground Theory Heights  Theta conj gauss Q re b971a3ac9b26: P2 M Ground Theory Heights  Theta conj gauss Q re b971a3ac9b26
-- statement:
--   The P2 M Ground Theory Heights  Theta conj gauss Q re b971a3ac9b26 construction uses the P2 M Ground Theory Heights  Theta conj gauss Q re b971a3ac9b26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L46-L47

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

theorem P2M_GroundTheory_Heights__Theta_conj_gaussQ_re_b971a3ac9b26 (z : GaussQ) : (conj ℚ GaussQ z).re = z.re := by sorry

alias «GroundTheory».«Heights₂».«Theta».«conj_gaussQ_re» := P2M_GroundTheory_Heights__Theta_conj_gaussQ_re_b971a3ac9b26
