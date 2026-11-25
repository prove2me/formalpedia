-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747
-- name    : P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:51:25.506262+00:00
-- url     : https://prove2.me/theorems/951b4c00-d796-45bb-8748-caeff949227a
-- title:
--   P2 M Ground Theory Heights  Theta Is Totally Isotropic le orth 45a92c67c747: P2 M Ground Theory Heights  Theta Is Totally Isotropic le orth 45a92c67c747
-- statement:
--   The P2 M Ground Theory Heights  Theta Is Totally Isotropic le orth 45a92c67c747 construction uses the P2 M Ground Theory Heights  Theta Is Totally Isotropic le orth 45a92c67c747 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L112-L114

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Parabolic
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
open Module Matrix TensorProduct GroundTheory.Automorphic NumberField
open scoped NumberField.AdeleRing
noncomputable section
set_option linter.unusedSectionVars false
open scoped Classical
variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E)
variable {K H}
variable (K H)
variable {K H}
variable (K H)
variable {K H}

theorem P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747 {W : Submodule E (ι → E)} (hW : IsTotallyIsotropic K H W) :
    W ≤ orth K H W := by sorry

alias «GroundTheory».«Heights₂».«Theta».«IsTotallyIsotropic».«le_orth» := P2M_GroundTheory_Heights__Theta_IsTotallyIsotropic_le_orth_45a92c67c747
