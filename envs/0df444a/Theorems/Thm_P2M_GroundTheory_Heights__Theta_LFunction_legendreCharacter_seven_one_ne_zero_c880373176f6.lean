-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_LFunction_legendreCharacter_seven_one_ne_zero_c880373176f6
-- name    : P2M_GroundTheory_Heights__Theta_LFunction_legendreCharacter_seven_one_ne_zero_c880373176f6
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:24.547286+00:00
-- url     : https://prove2.me/theorems/114c7ee2-315a-4ca8-b0ed-6f8ddeb42ecf
-- title:
--   P2 M Ground Theory Heights  Theta LFunction legendre Character seven one ne zero c880373176f6: P2 M Ground Theory Heights  Theta LFunction legendre Character seven one ne zero c880373176f6
-- statement:
--   The P2 M Ground Theory Heights  Theta LFunction legendre Character seven one ne zero c880373176f6 construction uses the P2 M Ground Theory Heights  Theta LFunction legendre Character seven one ne zero c880373176f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L128-L130

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

theorem P2M_GroundTheory_Heights__Theta_LFunction_legendreCharacter_seven_one_ne_zero_c880373176f6 :
    DirichletCharacter.LFunction (legendreCharacter 7) 1 ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«LFunction_legendreCharacter_seven_one_ne_zero» := P2M_GroundTheory_Heights__Theta_LFunction_legendreCharacter_seven_one_ne_zero_c880373176f6
