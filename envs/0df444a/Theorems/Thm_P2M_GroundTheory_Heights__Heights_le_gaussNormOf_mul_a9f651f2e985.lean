-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985
-- name    : P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:47:59.80643+00:00
-- url     : https://prove2.me/theorems/8870b20b-b2e1-46fe-930b-715719b056b8
-- title:
--   P2 M Ground Theory Heights  Heights le gauss Norm Of mul a9f651f2e985: P2 M Ground Theory Heights  Heights le gauss Norm Of mul a9f651f2e985
-- statement:
--   The P2 M Ground Theory Heights  Heights le gauss Norm Of mul a9f651f2e985 construction uses the P2 M Ground Theory Heights  Heights le gauss Norm Of mul a9f651f2e985 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L82-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L82-L143

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
variable {w}

theorem P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985 (hna : IsNonarchimedean w) {f g : MvPolynomial ι R} (hf : f ≠ 0)
    (hg : g ≠ 0) : gaussNormOf w f * gaussNormOf w g ≤ gaussNormOf w (f * g) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«le_gaussNormOf_mul» := P2M_GroundTheory_Heights__Heights_le_gaussNormOf_mul_a9f651f2e985
