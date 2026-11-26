-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_____chartProj_83976a02a6f6
-- name    : P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_____chartProj_83976a02a6f6
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:27.584353+00:00
-- url     : https://prove2.me/theorems/458328d1-da94-473a-a6b5-e3a075b90252
-- title:
--   P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart     chart Proj 83976a02a6f6: P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart     chart Proj 83976a02a6f6
-- statement:
--   The P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart     chart Proj 83976a02a6f6 construction uses the P2 M Ground Theory Heights  Theta Fibre Measure Is Trans Chart     chart Proj 83976a02a6f6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/ContinuousOnChartProjM.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Theta/EisensteinZeta/AdicFrames/ContinuousOnChartProjM.lean#L47-L48

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

theorem P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_____chartProj_83976a02a6f6 {X : G} (hX : X ∈ Ω) : σ (Γ X) (chartProj Γ σ X) = X := by sorry

alias «GroundTheory».«Heights₂».«Theta».«FibreMeasure».«IsTransChart».«σ_Γ_chartProj» := P2M_GroundTheory_Heights__Theta_FibreMeasure_IsTransChart_____chartProj_83976a02a6f6
