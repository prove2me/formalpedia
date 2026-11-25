-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_tubeDeep_term_0355a045511e
-- name    : P2M_GroundTheory_Heights__Heights_tubeDeep_term_0355a045511e
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:52:01.071886+00:00
-- url     : https://prove2.me/theorems/f3f426e5-6521-40e2-a060-7e273199018e
-- title:
--   P2 M Ground Theory Heights  Heights tube Deep term 0355a045511e: P2 M Ground Theory Heights  Heights tube Deep term 0355a045511e
-- statement:
--   The P2 M Ground Theory Heights  Heights tube Deep term 0355a045511e construction uses the P2 M Ground Theory Heights  Heights tube Deep term 0355a045511e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepMass.lean#L21-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTubeDeepMass.lean#L21-L55

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepRankOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepAreaCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepMass
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
open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_tubeDeep_term_0355a045511e (hR : TubeDeepRankOne.Statement) {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} {P : MvPolynomial (Fin (d + 1)) ℂ} {R : ℝ} {y : Fin (d + 1) → ℂ}
    {x : Fin n → ℂ} {s : (Fin (d + 1) → ℂ) → Fin n → ℂ} (hx : x ∈ fibre J A y) (hs : IsSheetAt J A x s)
    (hy : logAbsSq P y < -Real.exp 1) :
    |(Metric.closedBall 0 R).indicator (fun x => tubeWeight P (A *ᵥ x)) x *
        ReciprocityTheory.AnForm.maDens
          (fun k => vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y| =
      (Metric.closedBall (0 : Fin n → ℂ) R).indicator (fun _ => (1 : ℝ)) x *
        ∑ I : Fin d → Fin n, ‖deepJacDet P s I y‖ ^ 2 *
          ((2 / Real.pi) ^ (d + 1) * poincareDeepWeight (deepMap P s I y 0)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«tubeDeep_term» := P2M_GroundTheory_Heights__Heights_tubeDeep_term_0355a045511e
