-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:31:01.8597+00:00
-- url     : https://prove2.me/theorems/f0018d06-22e9-433a-9e9b-4c0b028716bb
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of le 2169d258a813: P2 M Ground Theory Heights  Heights gauss Norm Of le 2169d258a813
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of le 2169d258a813 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of le 2169d258a813 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L35-L40

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

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813 {f : MvPolynomial ι R} {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ m, w (f.coeff m) ≤ r) : gaussNormOf w f ≤ r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_le» := P2M_GroundTheory_Heights__Heights_gaussNormOf_le_2169d258a813
