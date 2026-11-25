-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_formV_sub_sum
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.formV_sub_sum
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:17.096941+00:00
-- url     : https://prove2.me/theorems/296a89ae-5ab9-571d-a7f7-fecda721e04a
-- title:
--   N: form V sub sum
-- statement:
--   The N construction uses the form V sub sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/ExistsCyclic.lean#L128-L133

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_ExistsCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.formV_sub_sum {m r : ℕ} (u w : Fin m → ℝ) (k : Fin r → ℝ) (g : Fin r → Fin m → ℝ) :
    formV (fun s => u s - ∑ b, k b * g b s) w = formV u w - ∑ b, k b * formV (g b) w := by sorry
