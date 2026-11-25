-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_num
-- name    : ReciprocityTheory.L2DbarEstimates.I.sh_num
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:00:50.215854+00:00
-- url     : https://prove2.me/theorems/30ae6485-f55f-58e0-824e-c3844c5764c1
-- title:
--   I: sh num
-- statement:
--   The I construction uses the sh num property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L108-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L108-L126

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ShellA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.I.sh_num (τ : ℝ) (hτ : 0 < τ) :
    Real.exp (min (τ / 10) (1 / 4)) * (Real.log 2 + 2 * min (τ / 10) (1 / 4)) ≤
      (1 + τ) * Real.log 2 := by sorry
