-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:05.558796+00:00
-- url     : https://prove2.me/theorems/2ca98065-0efc-42ad-bb9b-96fb657d5953
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of pos f7b56068fd3a: P2 M Ground Theory Heights  Heights gauss Norm Of pos f7b56068fd3a
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of pos f7b56068fd3a construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of pos f7b56068fd3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L50-L53

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

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a {f : MvPolynomial ι R} (hf : f ≠ 0) : 0 < gaussNormOf w f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_pos» := P2M_GroundTheory_Heights__Heights_gaussNormOf_pos_f7b56068fd3a
