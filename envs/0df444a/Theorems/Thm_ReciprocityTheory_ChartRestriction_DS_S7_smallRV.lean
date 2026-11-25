-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_smallRV
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.smallRV
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:50:57.610467+00:00
-- url     : https://prove2.me/theorems/d27fe761-a7db-5e10-86b6-79090680df88
-- title:
--   S7: small RV
-- statement:
--   The S7 construction uses the small RV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L303-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L303-L337

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
attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem ReciprocityTheory.ChartRestriction.DS.S7.smallRV {ε : Fin n → Bool} {s : Bool} {k : Matrix (Fin n) (Fin n) ℂ} (hk : inUJ ε k)
    {u v : Matrix (Fin n) (SgIxV ε s) ℂ} (hu : hsRV (u - signedIdentityColumns ε s) < 1 / 16) (hv : hsRV (v - signedIdentityColumns ε s) < 1 / 16)
    (h : k * u = v) : hs k ≤ n + 2 * (5 / 2 * Real.sqrt n + 1 / 2) ^ 2 := by sorry
