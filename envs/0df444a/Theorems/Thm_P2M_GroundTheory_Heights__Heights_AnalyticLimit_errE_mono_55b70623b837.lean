-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:33:52.419852+00:00
-- url     : https://prove2.me/theorems/9f73c471-af4c-5367-b2f5-718161f7bc2b
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit err E mono 55b70623b837: P2 M Ground Theory Heights  Heights Analytic Limit err E mono 55b70623b837
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit err E mono 55b70623b837 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit err E mono 55b70623b837 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L43-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837 {C C' t : ℝ} (hCC : C ≤ C') (h : 1 ≤ ell t) : errE C t ≤ errE C' t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«errE_mono» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_mono_55b70623b837
