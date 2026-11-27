-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_polyTower_nontrivial_4554658d4f8f
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_polyTower_nontrivial_4554658d4f8f
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:52.541405+00:00
-- url     : https://prove2.me/theorems/30eb36df-5c82-468c-be1d-241e4b05997e
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS poly Tower nontrivial 4554658d4f8f: P2 M Ground Theory Heights  Heights Effective HS poly Tower nontrivial 4554658d4f8f
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS poly Tower nontrivial 4554658d4f8f construction uses the P2 M Ground Theory Heights  Heights Effective HS poly Tower nontrivial 4554658d4f8f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L113-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L113-L125

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PConstants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_EffectiveHilbertSamuel_PDivision
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
open GroundTheory.Heights₂.Heights.EffectiveHS
open Finset

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_polyTower_nontrivial_4554658d4f8f :
    MvPolynomial.X 0 ∈ polyTower.W ∧ (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℚ) ≠ 0 ∧
      mono (fun i => MvPolynomial.X i) (fun _ => 1) * (∏ i : Fin 0, Fin.elim0 i) * 1 ∈
        polyTower.Vpp 2 2 2 (fun i => MvPolynomial.X i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«polyTower_nontrivial» := P2M_GroundTheory_Heights__Heights_EffectiveHS_polyTower_nontrivial_4554658d4f8f
