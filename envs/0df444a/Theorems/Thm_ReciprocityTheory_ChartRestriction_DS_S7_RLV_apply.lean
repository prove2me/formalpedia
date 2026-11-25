-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_RLV_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.RLV_apply
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:59.659868+00:00
-- url     : https://prove2.me/theorems/54a019ef-8364-41f4-9bac-c958363fd159
-- title:
--   S7: RLV apply
-- statement:
--   The S7 construction uses the RLV apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L259-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L259-L260

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.RLV_apply {Q : Type} [Fintype Q] (g : Matrix (Fin n) (Fin n) ℂ) (x : REV n Q) :
    RLV g x = Matrix.of.symm (g * Matrix.of x) := by sorry
