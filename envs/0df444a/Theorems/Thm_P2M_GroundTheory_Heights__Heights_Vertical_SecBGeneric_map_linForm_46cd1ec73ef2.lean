-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_linForm_46cd1ec73ef2
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_linForm_46cd1ec73ef2
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:44:18.460643+00:00
-- url     : https://prove2.me/theorems/fe0096b2-a589-5d32-b059-f59ec24fcbcd
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map lin Form 46cd1ec73ef2: P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map lin Form 46cd1ec73ef2
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map lin Form 46cd1ec73ef2 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BGeneric map lin Form 46cd1ec73ef2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBGeneric.lean#L28-L30

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_linForm_46cd1ec73ef2 {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBGeneric».«map_linForm» := P2M_GroundTheory_Heights__Heights_Vertical_SecBGeneric_map_linForm_46cd1ec73ef2
