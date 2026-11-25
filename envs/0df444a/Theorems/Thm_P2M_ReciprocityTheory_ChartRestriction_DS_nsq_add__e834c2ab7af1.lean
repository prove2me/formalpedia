-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1
-- name    : P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:12:49.884836+00:00
-- url     : https://prove2.me/theorems/cdaa721f-6721-4b1a-986a-b6cbcb49b67b
-- title:
--   P2 M Reciprocity Theory Chart Restriction DS nsq add  e834c2ab7af1: P2 M Reciprocity Theory Chart Restriction DS nsq add  e834c2ab7af1
-- statement:
--   The P2 M Reciprocity Theory Chart Restriction DS nsq add  e834c2ab7af1 construction uses the P2 M Reciprocity Theory Chart Restriction DS nsq add  e834c2ab7af1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L77-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L77-L79

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

theorem P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1 (x y : Fin n → ℝ) : nsq (x + y) = nsq x + 2 * dot x y + nsq y := by sorry

alias «ReciprocityTheory».«ChartRestriction».«DS».«nsq_add'» := P2M_ReciprocityTheory_ChartRestriction_DS_nsq_add__e834c2ab7af1
