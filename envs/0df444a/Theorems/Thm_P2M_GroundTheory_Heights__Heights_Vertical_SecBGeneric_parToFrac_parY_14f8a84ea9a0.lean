-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_parY_14f8a84ea9a0
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_parY_14f8a84ea9a0
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:07.227802+00:00
-- url     : https://prove2.me/theorems/540796e5-5770-479f-803a-a3146d86aac7
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac par Y 14f8a84ea9a0: P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac par Y 14f8a84ea9a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac par Y 14f8a84ea9a0 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BGeneric par To Frac par Y 14f8a84ea9a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L24-L26

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_parY_14f8a84ea9a0 (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBGeneric».«parToFrac_parY» := P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_parToFrac_parY_14f8a84ea9a0
