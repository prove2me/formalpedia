-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_wd_term
-- name    : ReciprocityTheory.ChartRestriction.DS.wd_term
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:55:08.676692+00:00
-- url     : https://prove2.me/theorems/3f5b22e9-b4b9-505f-b23a-204fbf3777b7
-- title:
--   DS: wd term
-- statement:
--   The DS construction uses the wd term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L100-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L100-L110

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
variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.wd_term (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M} (hU : IsInfUnitary ε E)
    {μ : Fin n → ℝ} {v : M} (hv : IsKHWVec ε E μ v) {a b : Fin n} (hab : wdP ε a b) :
    inner ℂ v (E b a (E a b v)) = ((-(if b < a ∧ ε b ≠ ε a then ‖E a b v‖ ^ 2 else 0) : ℝ) : ℂ) := by sorry
