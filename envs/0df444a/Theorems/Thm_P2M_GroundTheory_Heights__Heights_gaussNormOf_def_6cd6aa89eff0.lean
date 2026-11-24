-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0
-- name    : P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:32:04.023012+00:00
-- url     : https://prove2.me/theorems/7f96e93c-ec37-4b9f-836b-2443260f4b71
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm Of def 6cd6aa89eff0: P2 M Ground Theory Heights  Heights gauss Norm Of def 6cd6aa89eff0
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm Of def 6cd6aa89eff0 construction uses the P2 M Ground Theory Heights  Heights gauss Norm Of def 6cd6aa89eff0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L19-L21

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

theorem P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0 (f : MvPolynomial ι R) :
    gaussNormOf w f = (((f.support.sup fun m => (⟨w (f.coeff m), w.nonneg _⟩ : NNReal)) : NNReal) : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNormOf_def» := P2M_GroundTheory_Heights__Heights_gaussNormOf_def_6cd6aa89eff0
