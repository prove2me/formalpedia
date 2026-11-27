-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_add_left_df67c85d8297
-- name    : P2M_GroundTheory_Heights__Theta_hermPair_add_left_df67c85d8297
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:42:43.697903+00:00
-- url     : https://prove2.me/theorems/b373c346-f7e0-4078-b55a-405c8f292d0a
-- title:
--   P2 M Ground Theory Heights  Theta herm Pair add left df67c85d8297: P2 M Ground Theory Heights  Theta herm Pair add left df67c85d8297
-- statement:
--   The P2 M Ground Theory Heights  Theta herm Pair add left df67c85d8297 construction uses the P2 M Ground Theory Heights  Theta herm Pair add left df67c85d8297 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L39-L43

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

theorem P2M_GroundTheory_Heights__Theta_hermPair_add_left_df67c85d8297 (x y z : ι → E) :
    hermPair K H (x + y) z = hermPair K H x z + hermPair K H y z := by sorry

alias «GroundTheory».«Heights₂».«Theta».«hermPair_add_left» := P2M_GroundTheory_Heights__Theta_hermPair_add_left_df67c85d8297
