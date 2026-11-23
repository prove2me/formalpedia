-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_reindex
-- name    : ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:04.746245+00:00
-- url     : https://prove2.me/theorems/99ca2c3b-5297-41b6-af22-b4c1d86b83a1
-- title:
--   Flat Weighted Estimates: reindex
-- statement:
--   The Flat Weighted Estimates construction uses the reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/Localization/IntegrableFd.lean#L70-L73

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates

theorem ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.reindex {n : ℕ} (H : Fin n × Fin 2 → ℂ) :
    ∑ p : Fin (n * 2), H (finProdFinEquiv.symm p) = ∑ j, (H (j, 0) + H (j, 1)) := by sorry
