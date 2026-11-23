-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_db_subset
-- name    : ReciprocityTheory.L2DbarEstimates.tsupport_db_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:28:11.462808+00:00
-- url     : https://prove2.me/theorems/15160f4e-f83c-4ca6-ac18-0bece685f4ff
-- title:
--   L2 Dbar Estimates: tsupport db subset
-- statement:
--   The L2 Dbar Estimates construction uses the tsupport db subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L374-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L374-L390

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.tsupport_db_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) :
    tsupport (db n z j f) ⊆ tsupport f := by sorry
