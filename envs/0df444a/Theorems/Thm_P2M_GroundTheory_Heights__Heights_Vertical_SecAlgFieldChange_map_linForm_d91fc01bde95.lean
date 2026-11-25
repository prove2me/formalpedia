-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:43:16.519975+00:00
-- url     : https://prove2.me/theorems/e090575f-65d6-5405-b433-afe228e75653
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change map lin Form d91fc01bde95: P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change map lin Form d91fc01bde95
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change map lin Form d91fc01bde95 construction uses the P2 M Ground Theory Heights  Heights Vertical Sec Alg Field Change map lin Form d91fc01bde95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PSecAlgFieldChange.lean#L50-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_StatementsChowNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PSecAlgFieldChange
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
open MvPolynomial
open scoped TensorProduct
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.SecAlgFieldChange

theorem P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95 {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ}
    (u : Fin n → R) : MvPolynomial.map φ (linForm u) = linForm (φ ∘ u) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«SecAlgFieldChange».«map_linForm» := P2M_GroundTheory_Heights__Heights_Vertical_SecAlgFieldChange_map_linForm_d91fc01bde95
