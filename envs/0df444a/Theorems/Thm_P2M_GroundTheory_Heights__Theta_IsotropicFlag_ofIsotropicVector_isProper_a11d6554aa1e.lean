-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_IsotropicFlag_ofIsotropicVector_isProper_a11d6554aa1e
-- name    : P2M_GroundTheory_Heights__Theta_IsotropicFlag_ofIsotropicVector_isProper_a11d6554aa1e
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:51:47.405946+00:00
-- url     : https://prove2.me/theorems/6517a903-5e53-4a00-abcb-d693bfd4b310
-- title:
--   P2 M Ground Theory Heights  Theta Isotropic Flag of Isotropic Vector is Proper a11d6554aa1e: P2 M Ground Theory Heights  Theta Isotropic Flag of Isotropic Vector is Proper a11d6554aa1e
-- statement:
--   The P2 M Ground Theory Heights  Theta Isotropic Flag of Isotropic Vector is Proper a11d6554aa1e construction uses the P2 M Ground Theory Heights  Theta Isotropic Flag of Isotropic Vector is Proper a11d6554aa1e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L190-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/Parabolic.lean#L190-L193

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
open GroundTheory.Heights₂.Theta.IsotropicFlag

theorem P2M_GroundTheory_Heights__Theta_IsotropicFlag_ofIsotropicVector_isProper_a11d6554aa1e {x : ι → E} (hx : hermPair K H x x = 0) (hx0 : x ≠ 0) :
    (ofIsotropicVector hx).IsProper := by sorry

alias «GroundTheory».«Heights₂».«Theta».«IsotropicFlag».«ofIsotropicVector_isProper» := P2M_GroundTheory_Heights__Theta_IsotropicFlag_ofIsotropicVector_isProper_a11d6554aa1e
