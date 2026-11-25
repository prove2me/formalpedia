-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f
-- name    : P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:01:13.785591+00:00
-- url     : https://prove2.me/theorems/7fb9a56c-3f68-4785-9a72-6a8efbac9ace
-- title:
--   P2 M Ground Theory Heights  Theta Is Lattice Param smul fdb7c318695f: P2 M Ground Theory Heights  Theta Is Lattice Param smul fdb7c318695f
-- statement:
--   The P2 M Ground Theory Heights  Theta Is Lattice Param smul fdb7c318695f construction uses the P2 M Ground Theory Heights  Theta Is Lattice Param smul fdb7c318695f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L61-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L61-L77

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

theorem P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f {Λ : Set ℂ} {τ : ℍ} (h : IsLatticeParam Λ τ) (g : SL(2, ℤ)) :
    IsLatticeParam Λ (g • τ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«IsLatticeParam».«smul» := P2M_GroundTheory_Heights__Theta_IsLatticeParam_smul_fdb7c318695f
