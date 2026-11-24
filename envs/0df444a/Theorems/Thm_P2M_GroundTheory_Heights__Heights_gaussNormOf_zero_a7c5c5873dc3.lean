-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:56.660658+00:00
-- url     : https://prove2.me/theorems/90a8519a-55cf-4644-9cff-e20809999697
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of zero a7c5c5873dc3: P2 M Ground Theory Heights  Heights gauss Norm Of zero a7c5c5873dc3
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of zero a7c5c5873dc3 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of zero a7c5c5873dc3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L55-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L55-L56

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogGaussNormSupportFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {R : Type*} [CommRing R] {ι : Type*} (w : AbsoluteValue R ℝ)

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3 : gaussNormOf w (0 : MvPolynomial ι R) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_zero» := P2M_GroundTheory_Heights__Heights_gaussNormOf_zero_a7c5c5873dc3
