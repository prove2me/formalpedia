-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_mul_P0V_apply
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.mul_P0V_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:45:24.12538+00:00
-- url     : https://prove2.me/theorems/e6134cb6-99a3-4732-9aed-f5cd3baf13fd
-- title:
--   S7: mul P0 V apply
-- statement:
--   The S7 construction uses the mul P0 V apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L159-L161

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.mul_P0V_apply (ε : Fin n → Bool) (s : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (b : SgIxV ε s) :
    (g * signedIdentityColumns ε s) i b = g i b.1 := by sorry
