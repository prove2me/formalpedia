-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_mem_grpN_iff
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.mem_grpN_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:02:11.617628+00:00
-- url     : https://prove2.me/theorems/71934024-4577-48b3-ba06-e4975f56e2ee
-- title:
--   N: mem grp N iff
-- statement:
--   The N construction uses the mem grp N iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L688-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExpChart.lean#L688-L703

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExpChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
open Matrix
open scoped Matrix.Norms.Operator
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.mem_grpN_iff (lev : Fin n → ℕ) (H : Matrix (Fin n) (Fin n) ℂ) (hH : H * H = 1)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    g ∈ grpN (levF lev) (adjH H) ↔ g - 1 ∈ levF lev 0 ∧ gᴴ * H * g = H := by sorry
