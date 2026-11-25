-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333
-- name    : P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:54:23.739329+00:00
-- url     : https://prove2.me/theorems/4f9c1f24-cb6d-48b8-bafe-3124967d6a8a
-- title:
--   P2 M Ground Theory Heights  Theta span denom num eq 6cb8a20bd333: P2 M Ground Theory Heights  Theta span denom num eq 6cb8a20bd333
-- statement:
--   The P2 M Ground Theory Heights  Theta span denom num eq 6cb8a20bd333 construction uses the P2 M Ground Theory Heights  Theta span denom num eq 6cb8a20bd333 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L40-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L40-L59

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

theorem P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333 (g : SL(2, ℤ)) (τ : ℂ) :
    Submodule.span ℤ ({(g 1 0 : ℂ) * τ + g 1 1, (g 0 0 : ℂ) * τ + g 0 1} : Set ℂ) =
      Submodule.span ℤ ({1, τ} : Set ℂ) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«span_denom_num_eq» := P2M_GroundTheory_Heights__Theta_span_denom_num_eq_6cb8a20bd333
