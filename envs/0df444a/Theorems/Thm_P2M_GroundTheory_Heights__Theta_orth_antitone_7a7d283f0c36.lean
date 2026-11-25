-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
-- name    : P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:38.651804+00:00
-- url     : https://prove2.me/theorems/91fa7663-1710-4524-8e9b-32173f61de98
-- title:
--   P2 M Ground Theory Heights  Theta orth antitone 7a7d283f0c36: P2 M Ground Theory Heights  Theta orth antitone 7a7d283f0c36
-- statement:
--   The P2 M Ground Theory Heights  Theta orth antitone 7a7d283f0c36 construction uses the P2 M Ground Theory Heights  Theta orth antitone 7a7d283f0c36 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L91-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L91-L92

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

theorem P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36 {W W' : Submodule E (ι → E)} (h : W ≤ W') : orth K H W' ≤ orth K H W := by sorry

alias «GroundTheory».«Heights₂».«Theta».«orth_antitone» := P2M_GroundTheory_Heights__Theta_orth_antitone_7a7d283f0c36
