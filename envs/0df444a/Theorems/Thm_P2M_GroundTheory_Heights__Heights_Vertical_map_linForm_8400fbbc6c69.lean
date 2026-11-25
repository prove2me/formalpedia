-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:43:51.809847+00:00
-- url     : https://prove2.me/theorems/59999fe6-8788-4621-b35f-2610c0932c4d
-- title:
--   P2 M Ground Theory Heights  Heights Vertical map lin Form 8400fbbc6c69: P2 M Ground Theory Heights  Heights Vertical map lin Form 8400fbbc6c69
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical map lin Form 8400fbbc6c69 construction uses the P2 M Ground Theory Heights  Heights Vertical map lin Form 8400fbbc6c69 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSpecLength.lean#L53-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_IntToFracInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsOrd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSpecLength
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

theorem P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69 {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«map_linForm» := P2M_GroundTheory_Heights__Heights_Vertical_map_linForm_8400fbbc6c69
