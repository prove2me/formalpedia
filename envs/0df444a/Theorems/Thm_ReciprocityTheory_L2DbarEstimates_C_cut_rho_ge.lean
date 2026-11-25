-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_cut_rho_ge
-- name    : ReciprocityTheory.L2DbarEstimates.C.cut_rho_ge
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:08.333714+00:00
-- url     : https://prove2.me/theorems/b7761d75-f537-4c0a-8a21-3c14d521fee0
-- title:
--   C: cut rho ge
-- statement:
--   The C construction uses the cut rho ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L65-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L65-L71

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.C.cut_rho_ge {ε s : ℝ} (hε : 0 < ε) (hs : ε ≤ s) :
    s⁻¹ ≤ 4 * (s * halfLogRatioSqSecondDeriv ε s + halfLogRatioSqDeriv ε s) := by sorry
