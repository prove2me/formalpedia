-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_comp_algebraMap_6658d5377151
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_comp_algebraMap_6658d5377151
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:33.67543+00:00
-- url     : https://prove2.me/theorems/0e07adf5-2b9b-4bcd-9b2c-8452da863c03
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac comp algebra Map 6658d5377151: P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac comp algebra Map 6658d5377151
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac comp algebra Map 6658d5377151 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac comp algebra Map 6658d5377151 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L15-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L15-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial NumberField IsDedekindDomain
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecBGeneric
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_comp_algebraMap_6658d5377151 (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (parToFrac e n v).comp (algebraMap (𝓞 K) (ParDVR e n v)) =
      (kToFrac K e n).comp (algebraMap (𝓞 K) K) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBGeneric».«parToFrac_comp_algebraMap» := P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_comp_algebraMap_6658d5377151
