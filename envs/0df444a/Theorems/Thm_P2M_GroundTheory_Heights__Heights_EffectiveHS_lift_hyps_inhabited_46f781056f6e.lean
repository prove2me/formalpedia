-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e
-- name    : P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:10:33.609997+00:00
-- url     : https://prove2.me/theorems/85e32666-93d3-46a6-8272-3447a0107544
-- title:
--   P2 M Ground Theory Heights  Heights Effective HS lift hyps inhabited 46f781056f6e: P2 M Ground Theory Heights  Heights Effective HS lift hyps inhabited 46f781056f6e
-- statement:
--   The P2 M Ground Theory Heights  Heights Effective HS lift hyps inhabited 46f781056f6e construction uses the P2 M Ground Theory Heights  Heights Effective HS lift hyps inhabited 46f781056f6e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L199-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/EffectiveHilbertSamuel/PDivision.lean#L199-L207

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
open MeasureTheory

theorem P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e :
    (∀ (i : Fin 1) (x : Unit), ‖(fun _ _ => (1 : ℂ)) i x‖ ≤ (fun _ => (1 : ℝ)) i) ∧
    (∀ i : Fin 1, Integrable (fun x : Unit => ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2)
      (Measure.dirac ())) ∧
    (∀ i : Fin 1, ∫ x : Unit, ‖(fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ()) ≤
      (1 : ℝ) * (fun _ => (1 : ℝ)) i ^ 2) ∧
    ((1 : ℝ) ^ 2 ≤ 1 * ∫ x : Unit, ‖∑ i : Fin 1, (fun _ _ => (1 : ℂ)) i x *
      (fun _ _ => (1 : ℂ)) i x‖ ^ 2 ∂(Measure.dirac ())) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«EffectiveHS».«lift_hyps_inhabited» := P2M_GroundTheory_Heights__Heights_EffectiveHS_lift_hyps_inhabited_46f781056f6e
