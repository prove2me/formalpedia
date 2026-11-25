-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:23.823641+00:00
-- url     : https://prove2.me/theorems/74bce961-cfac-5fec-acc7-9086c7ca751c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous lin Form f08d93cacfab: P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous lin Form f08d93cacfab
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous lin Form f08d93cacfab construction uses the P2 M Ground Theory Heights  Heights Vertical Sec BFinite is Homogeneous lin Form f08d93cacfab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecBFinite.lean#L23-L24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecBFinite
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
open GroundTheory.Heights₂.Heights.Vertical.SecBFinite
variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab {n : ℕ} (u : Fin n → R) : (linForm u).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecBFinite».«isHomogeneous_linForm» := P2M_GroundTheory_Heights__Heights_Vertical_SecBFinite_isHomogeneous_linForm_f08d93cacfab
