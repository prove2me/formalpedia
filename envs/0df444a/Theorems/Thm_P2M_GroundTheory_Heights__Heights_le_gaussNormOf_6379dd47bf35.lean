-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
-- name    : P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:30:55.600042+00:00
-- url     : https://prove2.me/theorems/f6915d76-afe7-4384-aa04-afbf00598348
-- title:
--   P2 M Ground Theory Heights  Heights le gauss Norm Of 6379dd47bf35: P2 M Ground Theory Heights  Heights le gauss Norm Of 6379dd47bf35
-- statement:
--   The P2 M Ground Theory Heights  Heights le gauss Norm Of 6379dd47bf35 construction uses the P2 M Ground Theory Heights  Heights le gauss Norm Of 6379dd47bf35 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L25-L33

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

theorem P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35 (f : MvPolynomial ι R) (m : ι →₀ ℕ) : w (f.coeff m) ≤ gaussNormOf w f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_gaussNormOf» := P2M_GroundTheory_Heights__Heights_le_gaussNormOf_6379dd47bf35
