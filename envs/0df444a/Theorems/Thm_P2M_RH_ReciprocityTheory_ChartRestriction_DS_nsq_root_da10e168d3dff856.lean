-- Prove2me | Theorems.Thm_P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856
-- name    : P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:14.155307+00:00
-- url     : https://prove2.me/theorems/e5bcc5ff-58bd-488f-b389-e993e8d46dcb
-- title:
--   P2 M RH Reciprocity Theory Chart Restriction DS nsq root da10e168d3dff856: P2 M RH Reciprocity Theory Chart Restriction DS nsq root da10e168d3dff856
-- statement:
--   The P2 M RH Reciprocity Theory Chart Restriction DS nsq root da10e168d3dff856 construction uses the P2 M RH Reciprocity Theory Chart Restriction DS nsq root da10e168d3dff856 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L89-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L89-L91

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856 {a b : Fin n} (hab : a ≠ b) : nsq (root a b) = 2 := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«nsq_root» := P2M_RH_ReciprocityTheory_ChartRestriction_DS_nsq_root_da10e168d3dff856
