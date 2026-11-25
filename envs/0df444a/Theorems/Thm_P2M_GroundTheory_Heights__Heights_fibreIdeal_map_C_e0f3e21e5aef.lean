-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef
-- name    : P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:53.893173+00:00
-- url     : https://prove2.me/theorems/d824c10e-5804-59f3-b481-bfe94b73f4b5
-- title:
--   P2 M Ground Theory Heights  Heights fibre Ideal map C e0f3e21e5aef: P2 M Ground Theory Heights  Heights fibre Ideal map C e0f3e21e5aef
-- statement:
--   The P2 M Ground Theory Heights  Heights fibre Ideal map C e0f3e21e5aef construction uses the P2 M Ground Theory Heights  Heights fibre Ideal map C e0f3e21e5aef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreRadicalAway.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StGenericFibreRadicalAway.lean#L17-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericFibreRadicalAway
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef {σ : Type*} {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (t : σ → ℂ) :
    fibreIdeal (J.map (MvPolynomial.map (C : ℂ →+* MvPolynomial σ ℂ))) t = J := by sorry

alias «GroundTheory».«Heights₂».«Heights».«fibreIdeal_map_C» := P2M_GroundTheory_Heights__Heights_fibreIdeal_map_C_e0f3e21e5aef
