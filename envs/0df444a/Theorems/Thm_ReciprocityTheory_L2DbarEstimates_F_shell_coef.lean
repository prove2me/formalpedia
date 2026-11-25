-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_shell_coef
-- name    : ReciprocityTheory.L2DbarEstimates.F.shell_coef
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:48.708884+00:00
-- url     : https://prove2.me/theorems/6ae1092c-6b9b-44fa-a5f5-694fb106eee7
-- title:
--   F: shell coef
-- statement:
--   The F construction uses the shell coef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ShellCeilEq.lean#L23-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/ShellCeilEq.lean#L23-L35

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ShellCeilEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.F.shell_coef (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    ENNReal.ofReal (Real.exp (-(Real.log (1 + C) + k))) * ENNReal.ofReal C ≤
      ENNReal.ofReal (Real.exp (-(k : ℝ))) := by sorry
