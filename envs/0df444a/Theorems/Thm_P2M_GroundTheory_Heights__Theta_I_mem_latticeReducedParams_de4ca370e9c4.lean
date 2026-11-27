-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_I_mem_latticeReducedParams_de4ca370e9c4
-- name    : P2M_GroundTheory_Heights__Theta_I_mem_latticeReducedParams_de4ca370e9c4
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:03.368379+00:00
-- url     : https://prove2.me/theorems/33cd0c82-a5cc-5b0c-82f1-ef5856ed0283
-- title:
--   P2 M Ground Theory Heights  Theta I mem lattice Reduced Params de4ca370e9c4: P2 M Ground Theory Heights  Theta I mem lattice Reduced Params de4ca370e9c4
-- statement:
--   The P2 M Ground Theory Heights  Theta I mem lattice Reduced Params de4ca370e9c4 construction uses the P2 M Ground Theory Heights  Theta I mem lattice Reduced Params de4ca370e9c4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmStatements.lean#L106-L108

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

theorem P2M_GroundTheory_Heights__Theta_I_mem_latticeReducedParams_de4ca370e9c4 :
    UpperHalfPlane.I ∈ latticeReducedParams (latticeOf Complex.I) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«I_mem_latticeReducedParams» := P2M_GroundTheory_Heights__Theta_I_mem_latticeReducedParams_de4ca370e9c4
