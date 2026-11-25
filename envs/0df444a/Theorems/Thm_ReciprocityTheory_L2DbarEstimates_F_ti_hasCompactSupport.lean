-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_ti_hasCompactSupport
-- name    : ReciprocityTheory.L2DbarEstimates.F.ti_hasCompactSupport
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:02.363432+00:00
-- url     : https://prove2.me/theorems/fc188882-cb22-5cd6-89c0-32f081640a33
-- title:
--   F: ti has Compact Support
-- statement:
--   The F construction uses the ti has Compact Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/TestIneq.lean#L25-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/TestIneq.lean#L25-L40

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_TestIneq
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

theorem ReciprocityTheory.L2DbarEstimates.F.ti_hasCompactSupport {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → V n) (hf : IsTestForm n z f) : HasCompactSupport f := by sorry
