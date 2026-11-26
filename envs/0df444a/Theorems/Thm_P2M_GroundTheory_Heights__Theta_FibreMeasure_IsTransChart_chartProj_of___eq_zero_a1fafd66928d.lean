-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj_of___eq_zero_a1fafd66928d
-- name    : P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj_of___eq_zero_a1fafd66928d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:04.013024+00:00
-- url     : https://prove2.me/theorems/308bb276-c1d9-5aaa-96d9-dad622c300b5
-- title:
--   P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart chart Proj of   eq zero a1fafd66928d: P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart chart Proj of   eq zero a1fafd66928d
-- statement:
--   The P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart chart Proj of   eq zero a1fafd66928d construction uses the P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart chart Proj of   eq zero a1fafd66928d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/ContinuousOnChartProjM.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/ContinuousOnChartProjM.lean#L56-L57

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_AdicFrames_ContinuousOnChartProjM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FibreMeasure
open MeasureTheory Topology Filter Set
variable {G T : Type*}
  [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
  [T2Space T] [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
variable {dX : Measure G} {Γ : G → T} {Ω : Set G} {σ : T → G → G}
open GroundTheory.Heights₂.Theta.FibreMeasure.IsTransChart
variable (h : IsTransChart dX Γ Ω σ)
include h

theorem P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj_of___eq_zero_a1fafd66928d {X : G} (hX : X ∈ Ω) (h0 : Γ X = 0) : chartProj Γ σ X = X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FibreMeasure».«IsTransChart».«chartProj_of_Γ_eq_zero» := P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_chartProj_of___eq_zero_a1fafd66928d
