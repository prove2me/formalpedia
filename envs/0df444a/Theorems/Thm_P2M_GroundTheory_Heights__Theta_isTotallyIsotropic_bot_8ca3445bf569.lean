-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_isTotallyIsotropic_bot_8ca3445bf569
-- name    : P2M_GroundTheory_Heights__Theta_isTotallyIsotropic_bot_8ca3445bf569
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:54:18.552817+00:00
-- url     : https://prove2.me/theorems/6d3f7555-c601-4441-bb96-c1caf6f7f9b7
-- title:
--   P2 M Ground Theory Heights  Theta is Totally Isotropic bot 8ca3445bf569: P2 M Ground Theory Heights  Theta is Totally Isotropic bot 8ca3445bf569
-- statement:
--   The P2 M Ground Theory Heights  Theta is Totally Isotropic bot 8ca3445bf569 construction uses the P2 M Ground Theory Heights  Theta is Totally Isotropic bot 8ca3445bf569 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L116-L120

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

theorem P2M_GroundTheory_Heights__Theta_isTotallyIsotropic_bot_8ca3445bf569 : IsTotallyIsotropic K H (⊥ : Submodule E (ι → E)) := by sorry

alias «GroundTheory».«Heights₂».«Theta».«isTotallyIsotropic_bot» := P2M_GroundTheory_Heights__Theta_isTotallyIsotropic_bot_8ca3445bf569
