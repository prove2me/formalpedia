-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_lowK_sub_root_eq_zero
-- name    : ReciprocityTheory.ChartRestriction.DS.khw_lowK_sub_root_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:52:00.007412+00:00
-- url     : https://prove2.me/theorems/258b92c3-d1cc-4e73-815e-41415a5e43ba
-- title:
--   DS: khw low K sub root eq zero
-- statement:
--   The DS construction uses the khw low K sub root eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L171-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/KhwLowKSubRootEqZero.lean#L171-L186

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

theorem ReciprocityTheory.ChartRestriction.DS.khw_lowK_sub_root_eq_zero (ε : Fin n → Bool) {E : Fin n → Fin n → Module.End ℂ M}
    (hE : IsGlRep E) (hU : IsInfUnitary ε E) (lam : Fin n → ℝ) {a b : Fin n} (hab : a < b)
    (hε : ε a ≠ ε b) (hgap : 1 + 2 * dot (rhoC ε) (rhoN ε) < dot lam (root a b)) {v : M}
    (hv : IsKHWVec ε E (lowK ε lam - root a b) v)
    (hc : casimir E v = (casVal lam : ℂ) • v) : v = 0 := by sorry
