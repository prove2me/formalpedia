-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_sum_SgIxV
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.sum_SgIxV
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:27.845421+00:00
-- url     : https://prove2.me/theorems/bdfc9452-7b9a-554a-935a-0f0c2f8272a8
-- title:
--   S7: sum Sg Ix V
-- statement:
--   The S7 construction uses the sum Sg Ix V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L163-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L163-L166

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedEmbeddingToM
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_SignedIdentityColumns
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory Matrix Topology Metric Kronecker
open scoped ENNReal NNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.sum_SgIxV (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℝ) :
    ∑ b : SgIxV ε s, f b.1 = ∑ j, if ε j = s then f j else 0 := by sorry
