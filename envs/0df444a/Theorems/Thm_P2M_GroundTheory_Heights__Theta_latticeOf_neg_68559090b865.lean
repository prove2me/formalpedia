-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865
-- name    : P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:13.333158+00:00
-- url     : https://prove2.me/theorems/3b6dc9e7-2d5a-4526-b972-2b8c6fef24f7
-- title:
--   P2 M Ground Theory Heights  Theta lattice Of neg 68559090b865: P2 M Ground Theory Heights  Theta lattice Of neg 68559090b865
-- statement:
--   The P2 M Ground Theory Heights  Theta lattice Of neg 68559090b865 construction uses the P2 M Ground Theory Heights  Theta lattice Of neg 68559090b865 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L25-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L25-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_CfunOmClassReducedParamsNonemptyPf
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
open UpperHalfPlane ModularGroup Complex NumberField
open scoped Real MatrixGroups nonZeroDivisors

theorem P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865 (t : ℂ) : latticeOf (-t) = latticeOf t := by sorry

alias «GroundTheory».«Heights₂».«Theta».«latticeOf_neg» := P2M_GroundTheory_Heights__Theta_latticeOf_neg_68559090b865
