-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_secIdeal_943985cf5c6c
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_secIdeal_943985cf5c6c
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:43:16.546267+00:00
-- url     : https://prove2.me/theorems/8680aa2b-3230-404b-b990-99b495e80448
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map sec Ideal 943985cf5c6c: P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map sec Ideal 943985cf5c6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map sec Ideal 943985cf5c6c construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map sec Ideal 943985cf5c6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L57-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L57-L77

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_secIdeal_943985cf5c6c {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (secIdeal (modelR e I v) (parY e n v)).map (MvPolynomial.map (parToFrac e n v)) =
      secIdeal (idealF e I) (parYF K e n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBGeneric».«map_secIdeal» := P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_secIdeal_943985cf5c6c
