-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_integral_fsDens
-- name    : ReciprocityTheory.AnForm.integral_fsDens
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:13.298892+00:00
-- url     : https://prove2.me/theorems/b911ad30-8636-434c-a973-b5dad492fdd6
-- title:
--   An Form: integral fs Dens
-- statement:
--   The An Form construction uses the integral fs Dens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L153-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L153-L166

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section

theorem ReciprocityTheory.AnForm.integral_fsDens : ∫ z : ℂ, fsDens z = 1 := by sorry
