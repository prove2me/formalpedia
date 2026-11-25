-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_sch_gap
-- name    : ReciprocityTheory.ChartRestriction.DS.sch_gap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:48.0332+00:00
-- url     : https://prove2.me/theorems/994bd1fb-81e3-4451-9320-5c87e9704dd7
-- title:
--   DS: sch gap
-- statement:
--   The DS construction uses the sch gap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L101-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/Numerics.lean#L101-L108

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_NumRho
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_Numerics
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
variable {ε : Fin n → Bool}

theorem ReciprocityTheory.ChartRestriction.DS.sch_gap {lam : Fin n → ℝ} (hgap : StdGap ε lam) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b) := by sorry
