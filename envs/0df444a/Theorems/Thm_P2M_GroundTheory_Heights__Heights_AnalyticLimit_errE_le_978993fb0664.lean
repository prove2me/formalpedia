-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:28:47.192819+00:00
-- url     : https://prove2.me/theorems/e6f86e1b-edea-5d59-a58e-1f0e3c854011
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit err E le 978993fb0664: P2 M Ground Theory Heights  Heights Analytic Limit err E le 978993fb0664
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit err E le 978993fb0664 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit err E le 978993fb0664 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L38-L41

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

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664 {C t : ℝ} (hC : 0 ≤ C) (h : 1 ≤ ell t) : errE C t ≤ C := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«errE_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_errE_le_978993fb0664
