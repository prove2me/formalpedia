-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_covDet
-- name    : ReciprocityTheory.L2DbarEstimates.I.covDet
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:58.643887+00:00
-- url     : https://prove2.me/theorems/c2652075-da18-5fc1-8e58-de3b34728bcd
-- title:
--   I: cov Det
-- statement:
--   The I construction uses the cov Det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/CovDet.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/CovDet.lean#L10-L14

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_CovDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.covDet (n : ℕ) (f' : V n →L[ℂ] V n) :
    |(f'.restrictScalars ℝ : V n →L[ℝ] V n).det| =
      ‖LinearMap.det (f' : V n →ₗ[ℂ] V n)‖ ^ 2 := by sorry
