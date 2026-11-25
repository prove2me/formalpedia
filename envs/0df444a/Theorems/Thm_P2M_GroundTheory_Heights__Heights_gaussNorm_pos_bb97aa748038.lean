-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:24.637401+00:00
-- url     : https://prove2.me/theorems/d4299c6c-7543-4113-be5d-45e6a61b1765
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm pos bb97aa748038: P2 M Ground Theory Heights  Heights gauss Norm pos bb97aa748038
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm pos bb97aa748038 construction uses the P2 M Ground Theory Heights  Heights gauss Norm pos bb97aa748038 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L179-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L179-L180

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
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    {f : MvPolynomial ι K} (hf : f ≠ 0) : 0 < gaussNorm v f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_pos» := P2M_GroundTheory_Heights__Heights_gaussNorm_pos_bb97aa748038
