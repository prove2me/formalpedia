-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isotropic_gramIso_7ab060123dc5
-- name    : P2M_GroundTheory_Heights__Theta_isotropic_gramIso_7ab060123dc5
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:42:34.842987+00:00
-- url     : https://prove2.me/theorems/bb42d72c-d557-4c61-8e08-ebdd245f41a9
-- title:
--   P2 M Ground Theory Heights  Theta isotropic gram Iso 7ab060123dc5: P2 M Ground Theory Heights  Theta isotropic gram Iso 7ab060123dc5
-- statement:
--   The P2 M Ground Theory Heights  Theta isotropic gram Iso 7ab060123dc5 construction uses the P2 M Ground Theory Heights  Theta isotropic gram Iso 7ab060123dc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/GaussianExample.lean#L100-L103

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

theorem P2M_GroundTheory_Heights__Theta_isotropic_gramIso_7ab060123dc5 : (![1, 1] : Fin 2 → GaussQ) ≠ 0 ∧ gaussValue gramIso ![1, 1] = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isotropic_gramIso» := P2M_GroundTheory_Heights__Theta_isotropic_gramIso_7ab060123dc5
