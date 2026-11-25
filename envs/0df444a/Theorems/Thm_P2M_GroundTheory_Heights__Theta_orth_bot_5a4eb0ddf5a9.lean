-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_orth_bot_5a4eb0ddf5a9
-- name    : P2M_GroundTheory_Heights__Theta_orth_bot_5a4eb0ddf5a9
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:43:38.518063+00:00
-- url     : https://prove2.me/theorems/335ca74b-70aa-4a30-83df-84b14fb7f8ac
-- title:
--   P2 M Ground Theory Heights  Theta orth bot 5a4eb0ddf5a9: P2 M Ground Theory Heights  Theta orth bot 5a4eb0ddf5a9
-- statement:
--   The P2 M Ground Theory Heights  Theta orth bot 5a4eb0ddf5a9 construction uses the P2 M Ground Theory Heights  Theta orth bot 5a4eb0ddf5a9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L94-L97

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

theorem P2M_GroundTheory_Heights__Theta_orth_bot_5a4eb0ddf5a9 : orth K H (⊥ : Submodule E (ι → E)) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Theta».«orth_bot» := P2M_GroundTheory_Heights__Theta_orth_bot_5a4eb0ddf5a9
