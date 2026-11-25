-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_O_bddRV
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.O_bddRV
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:44:40.272399+00:00
-- url     : https://prove2.me/theorems/7a7acd0a-e7b1-4469-86c5-fe329114f745
-- title:
--   S7: O bdd RV
-- statement:
--   The S7 construction uses the O bdd RV property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L356-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/SignedIdentityColumns.lean#L356-L369

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

theorem ReciprocityTheory.ChartRestriction.DS.S7.O_bddRV {ε : Fin n → Bool} {s : Bool} {x : REV n (SgIxV ε s)} (hx : hsRV (Matrix.of x - signedIdentityColumns ε s) < 1 / 16) :
    x ∈ closedBall (0 : REV n (SgIxV ε s)) 2 := by sorry
