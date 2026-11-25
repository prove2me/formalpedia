-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_hermPair_zero_left_236801a17ead
-- name    : P2M_GroundTheory_Heights__Theta_hermPair_zero_left_236801a17ead
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:28:09.51054+00:00
-- url     : https://prove2.me/theorems/76cb5a00-76e0-4da0-b732-06b77511828d
-- title:
--   P2 M Ground Theory Heights  Theta herm Pair zero left 236801a17ead: P2 M Ground Theory Heights  Theta herm Pair zero left 236801a17ead
-- statement:
--   The P2 M Ground Theory Heights  Theta herm Pair zero left 236801a17ead construction uses the P2 M Ground Theory Heights  Theta herm Pair zero left 236801a17ead property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L51-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L51-L52

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

theorem P2M_GroundTheory_Heights__Theta_hermPair_zero_left_236801a17ead (y : ι → E) : hermPair K H 0 y = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«hermPair_zero_left» := P2M_GroundTheory_Heights__Theta_hermPair_zero_left_236801a17ead
