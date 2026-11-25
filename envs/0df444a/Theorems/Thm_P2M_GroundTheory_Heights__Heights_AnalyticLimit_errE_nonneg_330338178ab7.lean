-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:29:32.251713+00:00
-- url     : https://prove2.me/theorems/717ca9f3-002b-4fc1-a89b-27fd002106df
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit err E nonneg 330338178ab7: P2 M Ground Theory Heights  Heights Analytic Limit err E nonneg 330338178ab7
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit err E nonneg 330338178ab7 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit err E nonneg 330338178ab7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L35-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L35-L36

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7 {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : 0 ≤ errE C t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«errE_nonneg» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_nonneg_330338178ab7
