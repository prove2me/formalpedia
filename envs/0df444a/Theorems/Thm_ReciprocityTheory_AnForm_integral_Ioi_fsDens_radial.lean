-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_integral_Ioi_fsDens_radial
-- name    : ReciprocityTheory.AnForm.integral_Ioi_fsDens_radial
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:25.903395+00:00
-- url     : https://prove2.me/theorems/781fef3a-c179-4ddf-9ced-b1bbfaf7f276
-- title:
--   An Form: integral Ioi fs Dens radial
-- statement:
--   The An Form construction uses the integral Ioi fs Dens radial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L130-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/PotentialTheory/IntegralIoiFsDensRadial.lean#L130-L151

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

theorem ReciprocityTheory.AnForm.integral_Ioi_fsDens_radial :
    ∫ r in Ioi (0 : ℝ), r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)) = 1 / (2 * Real.pi) := by sorry
