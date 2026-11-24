-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
-- name    : P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:10.057983+00:00
-- url     : https://prove2.me/theorems/086126a8-03a5-4ffe-9728-0ca32af46ddf
-- title:
--   P2 M Ground Theory Heights  Heights gauss Norm eq gauss Norm Of d4ed71b31023: P2 M Ground Theory Heights  Heights gauss Norm eq gauss Norm Of d4ed71b31023
-- statement:
--   The P2 M Ground Theory Heights  Heights gauss Norm eq gauss Norm Of d4ed71b31023 construction uses the P2 M Ground Theory Heights  Heights gauss Norm eq gauss Norm Of d4ed71b31023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L159-L161

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

theorem P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023 (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ι : Type*}
    (f : MvPolynomial ι K) :
    gaussNorm v f = gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«gaussNorm_eq_gaussNormOf» := P2M_GroundTheory_Heights__Heights_gaussNorm_eq_gaussNormOf_d4ed71b31023
