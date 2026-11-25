-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:35:55.956728+00:00
-- url     : https://prove2.me/theorems/b7e41f56-b10d-5d1b-9d82-49d976f3ca62
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit two le smooth kb fd6647adc872: P2 M Ground Theory Heights  Heights Analytic Limit two le smooth kb fd6647adc872
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit two le smooth kb fd6647adc872 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit two le smooth kb fd6647adc872 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PKaehlerBound.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/PKaehlerBound.lean#L17-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_KaehlerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_PKaehlerBound
import Theorems.Thm_ReciprocityTheory_AnForm_continuousOn_levi
import Theorems.Thm_ReciprocityTheory_AnForm_levi_add_smul
import Theorems.Thm_ReciprocityTheory_AnForm_levi_comp
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_AnForm_levi_re_analytic
import Theorems.Thm_ReciprocityTheory_AnForm_levi_smul_dir
import Theorems.Thm_ReciprocityTheory_AnForm_levi_zero

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
open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi levi_congr levi_comp levi_zero levi_smul_dir levi_add_smul
  levi_re_analytic continuousOn_levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPosPot chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872 : (2 : WithTop ℕ∞) ≤ ∞ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«two_le_smooth_kb» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_two_le_smooth_kb_fd6647adc872
