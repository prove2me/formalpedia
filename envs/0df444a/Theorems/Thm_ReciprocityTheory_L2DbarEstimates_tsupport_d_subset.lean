-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_tsupport_d_subset
-- name    : ReciprocityTheory.L2DbarEstimates.tsupport_d_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:36:13.57369+00:00
-- url     : https://prove2.me/theorems/81b7158d-0592-4d7e-91b6-ad0facd43f4b
-- title:
--   L2 Dbar Estimates: tsupport d subset
-- statement:
--   The L2 Dbar Estimates construction uses the tsupport d subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L356-L372
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/TsupportDbSubset.lean#L356-L372

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_d

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

theorem ReciprocityTheory.L2DbarEstimates.tsupport_d_subset {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (j : Fin n) (f : M → ℂ) :
    tsupport (d n z j f) ⊆ tsupport f := by sorry
