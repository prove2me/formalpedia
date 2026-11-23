-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e
-- name    : P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:41:29.141251+00:00
-- url     : https://prove2.me/theorems/417ce00f-21e2-48c0-8537-46330a159b03
-- title:
--   P2 M Ground Theory Heights  Theta gauss Value diagonal ee78aa9b998e: P2 M Ground Theory Heights  Theta gauss Value diagonal ee78aa9b998e
-- statement:
--   The P2 M Ground Theory Heights  Theta gauss Value diagonal ee78aa9b998e construction uses the P2 M Ground Theory Heights  Theta gauss Value diagonal ee78aa9b998e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L59-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L59-L63

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

theorem P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e (d : Fin 2 → GaussQ) (x : Fin 2 → GaussQ) :
    gaussValue (Matrix.diagonal d) x =
      d 0 * (x 0 * conj ℚ GaussQ (x 0)) + d 1 * (x 1 * conj ℚ GaussQ (x 1)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«gaussValue_diagonal» := P2M_GroundTheory_Heights__Theta_gaussValue_diagonal_ee78aa9b998e
