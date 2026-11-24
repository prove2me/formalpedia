-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800
-- name    : P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:31.719799+00:00
-- url     : https://prove2.me/theorems/eedcde0c-32e1-4107-86b2-8fb682ab5d47
-- title:
--   P2 M Ground Theory Heights  Theta image mul span pair bc3f8dbd8800: P2 M Ground Theory Heights  Theta image mul span pair bc3f8dbd8800
-- statement:
--   The P2 M Ground Theory Heights  Theta image mul span pair bc3f8dbd8800 construction uses the P2 M Ground Theory Heights  Theta image mul span pair bc3f8dbd8800 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L12-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L12-L19

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

theorem P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800 (u a b : ℂ) :
    (fun z => u * z) '' (Submodule.span ℤ ({a, b} : Set ℂ) : Set ℂ) =
      (Submodule.span ℤ ({u * a, u * b} : Set ℂ) : Set ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«image_mul_span_pair» := P2M_GroundTheory_Heights__Theta_image_mul_span_pair_bc3f8dbd8800
