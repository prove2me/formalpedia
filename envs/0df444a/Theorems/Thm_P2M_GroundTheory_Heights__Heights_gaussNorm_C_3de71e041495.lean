-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:43:00.70839+00:00
-- url     : https://prove2.me/theorems/e8df750c-1d2e-45aa-a438-2704b66c7c5e
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm C 3de71e041495: P2 M Ground Theory Heights  Heights gauss Norm C 3de71e041495
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm C 3de71e041495 construction uses the P2 M Ground Theory Heights  Heights gauss Norm C 3de71e041495 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L167-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L167-L169

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

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*} (c : K) :
    gaussNorm v (C c : MvPolynomial ι K) = NumberField.HeightOneSpectrum.adicAbv K v c := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_C» := P2M_GroundTheory_Heights__Heights_gaussNorm_C_3de71e041495
