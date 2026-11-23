-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_hsRV_entry_le
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.hsRV_entry_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:21.303708+00:00
-- url     : https://prove2.me/theorems/7c77823e-a259-442f-9870-e25109055947
-- title:
--   S7: hs RV entry le
-- statement:
--   The S7 construction uses the hs RV entry le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L151-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L151-L157

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.hsRV_entry_le {Q : Type} [Fintype Q] (g : Matrix (Fin n) Q ℂ) (i : Fin n) (j : Q) : ‖g i j‖ ^ 2 ≤ hsRV g := by sorry
