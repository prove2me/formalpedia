-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696
-- name    : P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:28:30.15378+00:00
-- url     : https://prove2.me/theorems/27a907aa-18e1-453c-8eeb-521bc3ce363e
-- title:
--   P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count ball le 26a4f9913696: P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count ball le 26a4f9913696
-- statement:
--   The P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count ball le 26a4f9913696 construction uses the P2 M Ground Theory Heights  Heights Local Graph Mass frame Fibre Count ball le 26a4f9913696 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L150-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PLocalGraphMass.lean#L150-L167

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass
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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696 (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (S : Set (EuclideanSpace ℂ (Fin n))) (R : ℝ) (x : EuclideanSpace ℂ I) :
    frameFibreCount b I (S ∩ Metric.ball 0 R) (WithLp.ofLp x) ≤
      (Metric.ball (0 : EuclideanSpace ℂ I) R).indicator
        (fun _ => ⨆ y : I → ℂ, frameFibreCount b I S y) x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LocalGraphMass».«frameFibreCount_ball_le» := P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameFibreCount_ball_le_26a4f9913696
