-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:22.990403+00:00
-- url     : https://prove2.me/theorems/8021b815-35b3-40ca-9c3b-37044ac1f22e
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS nsq sub  a7aa378eee5a: P2 M Reciprocity Theory Chart Restriction DS nsq sub  a7aa378eee5a
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS nsq sub  a7aa378eee5a construction uses the P2 M Reciprocity Theory Chart Restriction DS nsq sub  a7aa378eee5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L81-L83

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a (x y : Fin n → ℝ) : nsq (x - y) = nsq x - 2 * dot x y + nsq y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«nsq_sub'» := P2M_ReciprocityTheory_ChartRestriction_DS_nsq_sub__a7aa378eee5a
