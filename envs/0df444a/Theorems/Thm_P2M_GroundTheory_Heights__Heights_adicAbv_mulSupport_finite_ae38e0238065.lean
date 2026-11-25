-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065
-- name    : P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:56.114162+00:00
-- url     : https://prove2.me/theorems/55fb6f6f-0e11-5103-a84d-5a264ebe9c0b
-- title:
--   P2 M Ground Theory Heights  Heights adic Abv mul Support finite ae38e0238065: P2 M Ground Theory Heights  Heights adic Abv mul Support finite ae38e0238065
-- statement:
--   The P2 M Ground Theory Heights  Heights adic Abv mul Support finite ae38e0238065 construction uses the P2 M Ground Theory Heights  Heights adic Abv mul Support finite ae38e0238065 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L182-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LogGaussNormSupportFinite.lean#L182-L194

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

theorem P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065 {x : K} (hx : x ≠ 0) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) =>
      NumberField.HeightOneSpectrum.adicAbv K v x).Finite := by sorry

alias «GroundTheory».«Heights₂».«Heights».«adicAbv_mulSupport_finite» := P2M_GroundTheory_Heights__Heights_adicAbv_mulSupport_finite_ae38e0238065
