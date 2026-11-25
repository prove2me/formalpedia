-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_diag
-- name    : ReciprocityTheory.ChartRestriction.DS.wd_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:12.775887+00:00
-- url     : https://prove2.me/theorems/bef756fe-7881-464e-becc-cd1c13138a09
-- title:
--   DS: wd diag
-- statement:
--   The DS construction uses the wd diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L47-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L47-L62

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_RhoEqRhoCAddRhoN
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_KhwLowKSubRootEqZero
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

theorem ReciprocityTheory.ChartRestriction.DS.wd_diag (ε : Fin n → Bool) (μ : Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (μ a - μ b) = 2 * dot μ (rhoC ε - rhoN ε) := by sorry
