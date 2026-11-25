-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_khw_weight_eq_of_irr
-- name    : ReciprocityTheory.ChartRestriction.DS.khw_weight_eq_of_irr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:08.631567+00:00
-- url     : https://prove2.me/theorems/110fc2d5-d88c-476e-b1e3-d028dba49ec3
-- title:
--   DS: khw weight eq of irr
-- statement:
--   The DS construction uses the khw weight eq of irr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L188-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/BochnerInequality/KhwWeightEqOfIrr.lean#L188-L192

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_CasValK
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_CasimirKKhwVec
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_BochnerInequality_KhwWeightEqOfIrr
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
variable {X : Type*} [AddCommGroup X] [Module ℂ X] {ε : Fin n → Bool}
  {A : Fin n → Fin n → Module.End ℂ X} {Λ : Fin n → ℝ} {V : Submodule ℂ X}

theorem ReciprocityTheory.ChartRestriction.DS.khw_weight_eq_of_irr (hA : IsGlRep A) (hV : IsKIrrHW ε A Λ V) {u : X} (hu : u ∈ V)
    (hu0 : u ≠ 0) {ν : Fin n → ℝ} (hν : IsKHWVec ε A ν u) : ν = Λ := by sorry
