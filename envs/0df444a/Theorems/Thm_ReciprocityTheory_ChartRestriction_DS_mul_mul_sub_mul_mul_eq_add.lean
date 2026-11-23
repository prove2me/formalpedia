-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_mul_mul_sub_mul_mul_eq_add
-- name    : ReciprocityTheory.ChartRestriction.DS.mul_mul_sub_mul_mul_eq_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:12:01.062794+00:00
-- url     : https://prove2.me/theorems/5f23f4b5-0a3a-4059-9cb2-9933c992bdfb
-- title:
--   DS: mul mul sub mul mul eq add
-- statement:
--   The DS construction uses the mul mul sub mul mul eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L15-L17

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_IsInfUnitary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirAlgebra_MulMulSubMulMulEqAdd
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
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem ReciprocityTheory.ChartRestriction.DS.mul_mul_sub_mul_mul_eq_add {R : Type*} [Ring R] (X Y Z : R) :
    X * Y * Z - Z * (X * Y) = (X * Z - Z * X) * Y + X * (Y * Z - Z * Y) := by sorry
