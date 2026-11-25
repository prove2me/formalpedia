-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_val
-- name    : ReciprocityTheory.L2DbarEstimates.I.sh_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:04:27.220593+00:00
-- url     : https://prove2.me/theorems/d6e5aa18-732b-512a-a164-2097955fa613
-- title:
--   I: sh val
-- statement:
--   The I construction uses the sh val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L128-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L128-L141

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

theorem ReciprocityTheory.L2DbarEstimates.I.sh_val (n j : ℕ) (S r a b : ℝ) (hS : 0 < S) (hr : 0 < r) :
    Real.exp (-b - ((n : ℝ) + j) * a) * (S * Real.exp (-a) / r ^ 2) ^ (-(n : ℝ)) =
      r ^ (2 * n) * Real.exp (-b - (j : ℝ) * a) * S ^ (-(n : ℝ)) := by sorry
