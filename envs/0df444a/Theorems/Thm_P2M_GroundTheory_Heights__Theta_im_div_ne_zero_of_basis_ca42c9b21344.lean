-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344
-- name    : P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:53:34.289094+00:00
-- url     : https://prove2.me/theorems/09775d39-9534-5c25-8d1d-a1f3ddf52312
-- title:
--   P2 M Ground Theory Heights  Theta im div ne zero of basis ca42c9b21344: P2 M Ground Theory Heights  Theta im div ne zero of basis ca42c9b21344
-- statement:
--   The P2 M Ground Theory Heights  Theta im div ne zero of basis ca42c9b21344 construction uses the P2 M Ground Theory Heights  Theta im div ne zero of basis ca42c9b21344 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L81-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/MirabolicInduction/CfunOmClassReducedParamsNonemptyPf.lean#L81-L111

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
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344 (σ : K →+* ℂ) (hσ : ∃ x : K, (σ x).im ≠ 0)
    {ι : Type*} (b : Module.Basis ι ℚ K) (e : ι ≃ Fin 2) :
    (σ (b (e.symm 1)) / σ (b (e.symm 0))).im ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«im_div_ne_zero_of_basis» := P2M_GroundTheory_Heights__Theta_im_div_ne_zero_of_basis_ca42c9b21344
