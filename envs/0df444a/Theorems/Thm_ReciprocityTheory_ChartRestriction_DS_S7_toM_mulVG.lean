-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_toM_mulVG
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.toM_mulVG
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:46:34.720618+00:00
-- url     : https://prove2.me/theorems/dae51afc-e714-4e74-8ddf-fc2ffe24bd78
-- title:
--   S7: to M mul VG
-- statement:
--   The S7 construction uses the to M mul VG property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L36-L36

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.toM_mulVG {ε : Fin n → Bool} (g h : UJ ε) : toM (g * h) = toM g * toM h := by sorry
