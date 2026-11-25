-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582
-- name    : P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:48.712992+00:00
-- url     : https://prove2.me/theorems/1c0cb3c6-8501-497b-8185-6af6dd70ad9f
-- title:
--   P2 M Ground Theory Heights  Heights Chart Metric den scale 816ca627b582: P2 M Ground Theory Heights  Heights Chart Metric den scale 816ca627b582
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Metric den scale 816ca627b582 construction uses the P2 M Ground Theory Heights  Heights Chart Metric den scale 816ca627b582 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L64-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/NormSqEvalConeScale.lean#L64-L95

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_NormSqEvalConeScale
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.ChartMetric

theorem P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582 {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {P : ArithVariety n}
    (D : AddBlockData P) {d : ι → ℕ}
    {g : ((k : ι) → Fin (n k + 1)) → Fin (D.size + 1) → MvPolynomial (Coord n) ℤ}
    (hg : D.IsFormSystem d g) {r : ℕ} {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ}
    (hG : P.IsHomogGenerators G δ) (t : ι → ℂ) (ht : ∀ k, t k ≠ 0) (z : Cone n ℂ) :
    D.den d g G δ (fun k i ↦ t k * z k i) =
      (∏ k, ‖t k‖ ^ (2 * ((d k : ℤ) + D.deg k))) * D.den d g G δ z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartMetric».«den_scale» := P2M_GroundTheory_Heights__Heights_ChartMetric_den_scale_816ca627b582
