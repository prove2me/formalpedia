-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_signedOrder_iff_not_swap_of_ne
-- name    : ReciprocityTheory.ChartRestriction.DS.signedOrder_iff_not_swap_of_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:54:23.976+00:00
-- url     : https://prove2.me/theorems/9d590c9b-d407-4495-86f2-9e5aba09603d
-- title:
--   DS: signed Order iff not swap of ne
-- statement:
--   The DS construction uses the signed Order iff not swap of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L19-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L19-L27

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

theorem ReciprocityTheory.ChartRestriction.DS.signedOrder_iff_not_swap_of_ne (ε : Fin n → Bool) (a b : Fin n) (h : a ≠ b) : wdP ε a b ↔ ¬ wdP ε b a := by sorry
