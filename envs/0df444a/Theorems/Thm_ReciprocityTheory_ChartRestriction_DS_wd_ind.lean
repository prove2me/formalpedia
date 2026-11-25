-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_ind
-- name    : ReciprocityTheory.ChartRestriction.DS.wd_ind
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:55:25.697334+00:00
-- url     : https://prove2.me/theorems/5bca01e0-0b5f-46f1-9486-3b9ccb17486f
-- title:
--   DS: wd ind
-- statement:
--   The DS construction uses the wd ind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L29-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L29-L41

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

theorem ReciprocityTheory.ChartRestriction.DS.wd_ind (ε : Fin n → Bool) (a b : Fin n) :
    ((if wdP ε a b then (1:ℝ) else 0) - (if wdP ε b a then (1:ℝ) else 0)) =
    ((if a < b ∧ ε b = ε a then (1:ℝ) else 0) - (if b < a ∧ ε b = ε a then 1 else 0)) -
    ((if a < b ∧ ε b ≠ ε a then (1:ℝ) else 0) - (if b < a ∧ ε b ≠ ε a then 1 else 0)) := by sorry
