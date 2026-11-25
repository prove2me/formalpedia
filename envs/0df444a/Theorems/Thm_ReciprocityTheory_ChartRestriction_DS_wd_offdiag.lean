-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_offdiag
-- name    : ReciprocityTheory.ChartRestriction.DS.wd_offdiag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:29.42497+00:00
-- url     : https://prove2.me/theorems/cf6cf4b0-ca82-4227-8e96-ccbf7651f637
-- title:
--   DS: wd offdiag
-- statement:
--   The DS construction uses the wd offdiag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L64-L75

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

theorem ReciprocityTheory.ChartRestriction.DS.wd_offdiag (ε : Fin n → Bool) (f : Fin n → Fin n → ℝ) :
    ∑ a, ∑ b ∈ univ.filter (fun b => wdP ε a b), (if b < a ∧ ε b ≠ ε a then f a b else 0) =
      ∑ a, ∑ b ∈ univ.filter (fun b => a < b ∧ ε a ≠ ε b), f b a := by sorry
