-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_wvol_finiteOnCompacts
-- name    : ReciprocityTheory.L2DbarEstimates.F.wvol_finiteOnCompacts
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T10:57:33.56988+00:00
-- url     : https://prove2.me/theorems/5c4fbe63-6619-42e4-8114-a63d36842d03
-- title:
--   F: wvol finite On Compacts
-- statement:
--   The F construction uses the wvol finite On Compacts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/KPsiHasCompactSupport.lean#L11-L28

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_KPsiHasCompactSupport
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

theorem ReciprocityTheory.L2DbarEstimates.F.wvol_finiteOnCompacts {M : Type*} [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph : M → ℝ) (hph : Continuous ph) :
    IsFiniteMeasureOnCompacts (wvol n z ph) := by sorry
