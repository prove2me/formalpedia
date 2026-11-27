-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_analyticOnNhd_V_of_differentiableOn
-- name    : ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:23.205389+00:00
-- url     : https://prove2.me/theorems/fc245c01-7df1-47f1-b086-9d0b6096c04f
-- title:
--   Multiplicative Heights: analytic On Nhd V of differentiable On
-- statement:
--   The Multiplicative Heights construction uses the analytic On Nhd V of differentiable On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/ShareDetA.lean#L10-L21

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareDetA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix Filter Topology Set

theorem ReciprocityTheory.MultiplicativeHeights.analyticOnNhd_V_of_differentiableOn {n : ℕ} {f : ReciprocityTheory.L2DbarEstimates.V n → ℂ}
    {B : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hB : IsOpen B) (hf : DifferentiableOn ℂ f B) :
    AnalyticOnNhd ℂ f B := by sorry
