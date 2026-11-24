-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a
-- name    : P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:21.216291+00:00
-- url     : https://prove2.me/theorems/ea6e8211-1d53-40b6-911f-b73b72118328
-- title:
--   P2 M Ground Theory Heights  Theta eta Period pos b13a4c259a1a: P2 M Ground Theory Heights  Theta eta Period pos b13a4c259a1a
-- statement:
--   The P2 M Ground Theory Heights  Theta eta Period pos b13a4c259a1a construction uses the P2 M Ground Theory Heights  Theta eta Period pos b13a4c259a1a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L94-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L94-L99

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open UpperHalfPlane ModularGroup ModularForm Complex NumberField
open scoped Real Modular MatrixGroups nonZeroDivisors

theorem P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a (τ : ℍ) : 0 < etaPeriod τ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«etaPeriod_pos» := P2M_GroundTheory_Heights__Theta_etaPeriod_pos_b13a4c259a1a
