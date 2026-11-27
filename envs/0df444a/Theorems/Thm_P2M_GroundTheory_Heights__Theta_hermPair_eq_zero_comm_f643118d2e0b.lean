-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_eq_zero_comm_f643118d2e0b
-- name    : P2M_GroundTheory_Heights__Theta_hermPair_eq_zero_comm_f643118d2e0b
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:02.721817+00:00
-- url     : https://prove2.me/theorems/dea5e12f-7132-4492-be97-9b9f805f2958
-- title:
--   P2 M Ground Theory Heights  Theta herm Pair eq zero comm f643118d2e0b: P2 M Ground Theory Heights  Theta herm Pair eq zero comm f643118d2e0b
-- statement:
--   The P2 M Ground Theory Heights  Theta herm Pair eq zero comm f643118d2e0b construction uses the P2 M Ground Theory Heights  Theta herm Pair eq zero comm f643118d2e0b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L66-L74

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

theorem P2M_GroundTheory_Heights__Theta_hermPair_eq_zero_comm_f643118d2e0b (hH : IsHermitianFor (conjHom K E) H) {x y : ι → E} :
    hermPair K H y x = 0 ↔ hermPair K H x y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«hermPair_eq_zero_comm» := P2M_GroundTheory_Heights__Theta_hermPair_eq_zero_comm_f643118d2e0b
