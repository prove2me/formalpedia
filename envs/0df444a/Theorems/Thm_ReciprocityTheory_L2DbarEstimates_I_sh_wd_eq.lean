-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_sh_wd_eq
-- name    : ReciprocityTheory.L2DbarEstimates.I.sh_wd_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T10:58:32.855678+00:00
-- url     : https://prove2.me/theorems/60599503-f062-4e8d-b9d2-ddc81dc383f7
-- title:
--   I: sh wd eq
-- statement:
--   The I construction uses the sh wd eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ShellA.lean#L29-L36

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

theorem ReciprocityTheory.L2DbarEstimates.I.sh_wd_eq (n : ℕ) (j : Fin n) (f : V n → ℂ) (y : V n) (hf : DifferentiableAt ℂ f y) :
    wd n j f y = fderiv ℂ f y (bas n j) := by sorry
