-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e
-- name    : P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:02.988661+00:00
-- url     : https://prove2.me/theorems/8fb404bc-c2b9-48f5-be7b-8273b4361aa5
-- title:
--   P2 M Ground Theory Heights  Theta image mul lattice Of 7fca628f177e: P2 M Ground Theory Heights  Theta image mul lattice Of 7fca628f177e
-- statement:
--   The P2 M Ground Theory Heights  Theta image mul lattice Of 7fca628f177e construction uses the P2 M Ground Theory Heights  Theta image mul lattice Of 7fca628f177e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L21-L23

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

theorem P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e (u τ : ℂ) :
    (fun z => u * z) '' latticeOf τ = (Submodule.span ℤ ({u, u * τ} : Set ℂ) : Set ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«image_mul_latticeOf» := P2M_GroundTheory_Heights__Theta_image_mul_latticeOf_7fca628f177e
