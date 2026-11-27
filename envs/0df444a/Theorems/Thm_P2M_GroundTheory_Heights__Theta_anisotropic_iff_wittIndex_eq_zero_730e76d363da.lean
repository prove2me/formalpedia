-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_anisotropic_iff_wittIndex_eq_zero_730e76d363da
-- name    : P2M_GroundTheory_Heights__Theta_anisotropic_iff_wittIndex_eq_zero_730e76d363da
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:25.933364+00:00
-- url     : https://prove2.me/theorems/47812cbe-b33e-4622-8bf5-942623d5373e
-- title:
--   P2 M Ground Theory Heights  Theta anisotropic iff witt Index eq zero 730e76d363da: P2 M Ground Theory Heights  Theta anisotropic iff witt Index eq zero 730e76d363da
-- statement:
--   The P2 M Ground Theory Heights  Theta anisotropic iff witt Index eq zero 730e76d363da construction uses the P2 M Ground Theory Heights  Theta anisotropic iff witt Index eq zero 730e76d363da property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L140-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L140-L156

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

theorem P2M_GroundTheory_Heights__Theta_anisotropic_iff_wittIndex_eq_zero_730e76d363da : IsAnisotropic K H ↔ wittIndex K H = 0 := by sorry

alias «GroundTheory».«Heights₂».«Theta».«anisotropic_iff_wittIndex_eq_zero» := P2M_GroundTheory_Heights__Theta_anisotropic_iff_wittIndex_eq_zero_730e76d363da
