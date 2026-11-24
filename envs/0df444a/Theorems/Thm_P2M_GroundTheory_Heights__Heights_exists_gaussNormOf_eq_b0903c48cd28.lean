-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
-- name    : P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:04.190243+00:00
-- url     : https://prove2.me/theorems/07a4fb6e-db09-4e1b-8709-9c036ba797e5
-- title:
--   P2 M Ground Theory Heights  Heights exists gauss Norm Of eq b0903c48cd28: P2 M Ground Theory Heights  Heights exists gauss Norm Of eq b0903c48cd28
-- statement:
--   The P2 M Ground Theory Heights  Heights exists gauss Norm Of eq b0903c48cd28 construction uses the P2 M Ground Theory Heights  Heights exists gauss Norm Of eq b0903c48cd28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L42-L48

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

theorem P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28 {f : MvPolynomial ι R} (hf : f ≠ 0) :
    ∃ m ∈ f.support, gaussNormOf w f = w (f.coeff m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_gaussNormOf_eq» := P2M_GroundTheory_Heights__Heights_exists_gaussNormOf_eq_b0903c48cd28
