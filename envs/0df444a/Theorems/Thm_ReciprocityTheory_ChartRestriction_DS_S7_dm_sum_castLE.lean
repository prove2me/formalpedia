-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_dm_sum_castLE
-- name    : ReciprocityTheory.ChartRestriction.DS.S7.dm_sum_castLE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:48.200392+00:00
-- url     : https://prove2.me/theorems/74fc146b-b0b0-4e9d-9146-351a327f8e85
-- title:
--   S7: dm sum cast LE
-- statement:
--   The S7 construction uses the dm sum cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsA.lean#L24-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirCoefficients/DecMomentsA.lean#L24-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CBinet
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_DecMomentsA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}

theorem ReciprocityTheory.ChartRestriction.DS.S7.dm_sum_castLE {i : ℕ} (hi : i ≤ n) (f : Fin n → ℂ) :
    ∑ a : Fin i, f (Fin.castLE hi a) = ∑ a : Fin n, dmChi i a * f a := by sorry
