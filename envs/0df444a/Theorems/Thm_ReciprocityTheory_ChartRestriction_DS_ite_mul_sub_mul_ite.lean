-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_ite_mul_sub_mul_ite
-- name    : ReciprocityTheory.ChartRestriction.DS.ite_mul_sub_mul_ite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:36:55.6268+00:00
-- url     : https://prove2.me/theorems/0f644150-f690-4046-96c6-28b3d043aff5
-- title:
--   DS: ite mul sub mul ite
-- statement:
--   The DS construction uses the ite mul sub mul ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/CasimirAlgebra/MulMulSubMulMulEqAdd.lean#L19-L21

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

theorem ReciprocityTheory.ChartRestriction.DS.ite_mul_sub_mul_ite {R : Type*} [Ring R] (p : Prop) [Decidable p] (X Z : R) :
    (if p then X else 0) * Z - Z * (if p then X else 0) = if p then X * Z - Z * X else 0 := by sorry
