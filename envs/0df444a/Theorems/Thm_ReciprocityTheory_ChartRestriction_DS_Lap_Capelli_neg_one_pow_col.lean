-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_neg_one_pow_col
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.neg_one_pow_col
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:43:19.725269+00:00
-- url     : https://prove2.me/theorems/8771e404-65d9-5128-bbfd-29485cbb9caa
-- title:
--   Capelli: neg one pow col
-- statement:
--   The Capelli construction uses the neg one pow col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/CapelliIdentity/RowColA.lean#L70-L73

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowAnti
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_ProdOfFnUpdateEq
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowColA
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.neg_one_pow_col (a b c : ℕ) :
    (-1 : ℂ) ^ (a + b) * (-1 : ℂ) ^ (b + c + 1) = (-1 : ℂ) ^ (a + c + 1) := by sorry
